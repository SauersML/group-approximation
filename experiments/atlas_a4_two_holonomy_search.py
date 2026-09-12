#!/usr/bin/env python3
"""Bounded 15-point search for packet+19243 two-holonomy escapes.

This is a falsification tool, not a proof.  Put both copies of
``A8=GL(4,2)`` in the permutation representation on the fifteen nonzero
vectors, with relative unitary ``U``.  The objective rewards the real traces
of the thirty shortest A4 pair-cubes and collision ``q_19243`` while, for a
user-selected Lagrange multiplier, rewarding the two-holonomy energy

    E_2HOL = 2 delta_U(c)^2 + delta_U(a)^2.

The regular-amplified theorem in Cairn is representation-type sensitive, so a
bad point here does not refute that theorem.  It *does* refute any proposed
proof which uses only the abstract word equations and ignores the regular
character profile.  NumPy and 15-by-15 matrices keep each sweep deliberately
small enough for rapid MSI iteration.
"""

import argparse
import json
import os
import time

import numpy as np

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_t30_parabolic_c3_bridge import (
    H6_LABELS,
    H18_LABELS,
    I4 as I4_TUPLE,
    Q_FIRST_INVOLUTION,
    Q_SECOND,
    center,
    matrix_hex,
    subgroup,
)
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import (
    Problem,
    cayley_left,
    gf2_inv,
    gf2_mul,
    haar_unitary,
    matrix_key,
    permutation_rep,
)


REFERENCE_ALIGNMENT_HEX = "00000001000100000100000000000100"


def bridge_labels():
    h = np.array(H6_LABELS[2], dtype=np.uint8)
    k = np.array(Q_SECOND[0], dtype=np.uint8)
    c = gf2_mul(h, k)
    h18 = subgroup(H18_LABELS)
    z_values = sorted(
        (value for value in center(h18) if value != I4_TUPLE),
        key=matrix_hex,
    )
    z = np.array(z_values[0], dtype=np.uint8)
    b = np.array(Q_FIRST_INVOLUTION, dtype=np.uint8)
    a = gf2_mul(z, b)
    return c, a


def load_words():
    states, _ = enumerate_ball(5)
    spanning, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(spanning, x_lengths())
    packet_words = [word for _index, word in packet]
    packet_names = ["packet:%d" % index for index, _word in packet]

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])

    c, a = bridge_labels()
    covariance = [
        [(2, c), (1, gf2_inv(c))],
        [(2, a), (1, gf2_inv(a))],
    ]
    return packet_names + ["q:19243"], packet_words + [collision], covariance


class HolonomyProblem(Problem):
    """Reuse the exact cyclic word gradient from ``atlas_two_chart_search``."""

    def __init__(self):
        self.k = 1
        self.n = 15
        self.names, self.words, self.covariance_words = load_words()
        distinct = {}
        for word in self.words + self.covariance_words:
            for _factor, matrix in word:
                distinct.setdefault(matrix_key(matrix), matrix)
        self.reps = {
            key: permutation_rep(matrix)
            for key, matrix in distinct.items()
        }

    def traces_for(self, words, u, need_gradient=False):
        values = []
        gradients = []
        for word in words:
            value, gradient = self.word_trace_and_gradient(word, u, need_gradient)
            values.append(value)
            if need_gradient:
                gradients.append(gradient / self.n)
        return np.asarray(values), gradients

    def objective(self, u, multiplier, q_weight, need_gradient=False):
        traces, gradients = self.traces_for(self.words, u, need_gradient)
        covariance, cov_gradients = self.traces_for(
            self.covariance_words, u, need_gradient
        )
        # E_2HOL=2(2-2 tr_c)+(2-2 tr_a)=6-4 tr_c-2 tr_a.
        energy = 6.0 - 4.0 * covariance[0] - 2.0 * covariance[1]
        weights = np.ones(len(traces))
        weights[-1] = q_weight
        score = float(np.dot(weights, traces) / weights.sum() + multiplier * energy)
        if not need_gradient:
            return score, None
        gradient = sum(
            weight * gradient
            for weight, gradient in zip(weights, gradients)
        ) / weights.sum()
        gradient += multiplier * (-4.0 * cov_gradients[0] - 2.0 * cov_gradients[1])
        return score, gradient

    def diagnostics(self, u):
        traces, _ = self.traces_for(self.words, u)
        covariance, _ = self.traces_for(self.covariance_words, u)
        defects_squared = np.maximum(0.0, 2.0 - 2.0 * traces)
        packet = defects_squared[:-1]
        q_defect_squared = float(defects_squared[-1])
        energy = float(6.0 - 4.0 * covariance[0] - 2.0 * covariance[1])
        residual_sum = float(defects_squared.sum())
        worst = int(np.argmax(defects_squared))
        return {
            "packet_rms_defect": float(np.sqrt(packet.mean())),
            "packet_max_defect": float(np.sqrt(packet.max())),
            "q_defect": float(np.sqrt(q_defect_squared)),
            "joint_rms_defect": float(np.sqrt(defects_squared.mean())),
            "joint_max_defect": float(np.sqrt(defects_squared.max())),
            "joint_residual_sum": residual_sum,
            "two_holonomy_energy": energy,
            "energy_over_residual_sum": (
                energy / residual_sum if residual_sum > 1e-14 else None
            ),
            "worst_word": self.names[worst],
        }


def initial_unitary(kind, problem, rng):
    if kind == "random":
        return haar_unitary(problem.n, rng)
    if kind == "identity":
        return np.eye(problem.n, dtype=np.complex128)
    if kind == "reference":
        matrix = np.frombuffer(
            bytes.fromhex(REFERENCE_ALIGNMENT_HEX), dtype=np.uint8
        ).reshape(4, 4).copy()
        return permutation_rep(matrix)
    raise ValueError("unknown start %r" % kind)


def optimize(problem, seed, multiplier, q_weight, iterations, report_every, start):
    rng = np.random.default_rng(seed)
    u = initial_unitary(start, problem, rng)
    if seed != 19243:
        noise = rng.standard_normal((problem.n, problem.n))
        noise = noise + 1j * rng.standard_normal((problem.n, problem.n))
        kick = 0.5 * (noise - noise.conj().T) / np.sqrt(problem.n)
        u = cayley_left(u, kick, 1e-3)
    best_u = u.copy()
    best_score, _ = problem.objective(u, multiplier, q_weight)
    best_diagnostics = problem.diagnostics(u)
    started = time.time()
    for iteration in range(1, iterations + 1):
        old, gradient = problem.objective(u, multiplier, q_weight, True)
        skew = 0.5 * (gradient - gradient.conj().T)
        accepted = False
        # Test both signs.  This also makes the diagnostic robust to the
        # left/right gradient convention inherited from the older search.
        for sign in (-1.0, 1.0):
            for step in (3.0, 1.0, 0.3, 0.1, 0.03, 0.01, 0.003):
                candidate = cayley_left(u, sign * skew, step)
                new, _ = problem.objective(candidate, multiplier, q_weight)
                if new > old + 1e-12:
                    u = candidate
                    accepted = True
                    break
            if accepted:
                break
        if not accepted:
            noise = rng.standard_normal((problem.n, problem.n))
            noise = noise + 1j * rng.standard_normal((problem.n, problem.n))
            kick = 0.5 * (noise - noise.conj().T) / np.sqrt(problem.n)
            u = cayley_left(u, kick, 1e-4)

        if iteration % report_every == 0 or iteration == iterations:
            score, _ = problem.objective(u, multiplier, q_weight)
            diagnostics = problem.diagnostics(u)
            if score > best_score:
                best_score = score
                best_u = u.copy()
                best_diagnostics = diagnostics
            print(json.dumps({
                "event": "progress",
                "seed": seed,
                "multiplier": multiplier,
                "q_weight": q_weight,
                "start": start,
                "iteration": iteration,
                "elapsed_s": round(time.time() - started, 3),
                "score": score,
                **diagnostics
            }, sort_keys=True), flush=True)
    return best_u, best_score, best_diagnostics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--iters", type=int, default=120)
    parser.add_argument("--seeds", type=int, default=3)
    parser.add_argument("--report-every", type=int, default=40)
    parser.add_argument(
        "--multipliers",
        type=float,
        nargs="+",
        default=(0.0, 0.01, 0.03, 0.1),
    )
    parser.add_argument("--q-weights", type=float, nargs="+", default=(1.0, 30.0))
    parser.add_argument(
        "--starts", nargs="+", choices=("reference", "identity", "random"),
        default=("reference", "random")
    )
    parser.add_argument("--save")
    args = parser.parse_args()

    problem = HolonomyProblem()
    print(json.dumps({
        "event": "start",
        "dimension": problem.n,
        "packet_words": len(problem.words) - 1,
        "joint_words": len(problem.words),
        "multipliers": args.multipliers,
        "q_weights": args.q_weights,
        "starts": args.starts,
    }, sort_keys=True), flush=True)
    records = []
    for multiplier in args.multipliers:
        for q_weight in args.q_weights:
            for start in args.starts:
                for offset in range(args.seeds):
                    unitary, score, diagnostics = optimize(
                        problem,
                        19243 + offset,
                        multiplier,
                        q_weight,
                        args.iters,
                        args.report_every,
                        start,
                    )
                    records.append((
                        score, multiplier, q_weight, start, offset, unitary,
                        diagnostics
                    ))

    score, multiplier, q_weight, start, offset, unitary, diagnostics = max(
        records, key=lambda record: record[0]
    )
    if args.save:
        np.save(args.save, unitary)
    print(json.dumps({
        "event": "final",
        "best_score": score,
        "best_multiplier": multiplier,
        "best_q_weight": q_weight,
        "best_start": start,
        "best_seed_offset": offset,
        **diagnostics
    }, sort_keys=True), flush=True)


if __name__ == "__main__":
    main()
