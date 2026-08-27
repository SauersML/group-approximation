"""Continue the exact 64D phase seed over the full relative U(64).

The two A8 chart marginals remain the honest W=(5,2,1) representation.  Only
their relative unitary is varied.  For the first self-similarity survivor r,
the objective rewards the real traces of the twelve centrality commutators
and penalizes Re tr(r).  The latter is exactly a reward for normalized-HS
distance from the identity:

    ||r-I||_2^2 = 2 - 2 Re tr(r).

Scanning the phase weight therefore measures the actual Pareto gate between
global centrality and a macroscopic surviving relation.  The gradient is the
exact cyclic derivative and updates use unitary Cayley retractions.
"""

import argparse
import json
import math
import time

import numpy as np

from atlas_clifford_block import CliffordBlock
from atlas_two_chart_search import (
    cayley_left,
    commutator,
    factor_generators,
    gf2_mul,
    matrix_key,
    transvection,
)


def survivor_word():
    a = transvection(1, 0)
    b = transvection(0, 1)
    c = transvection(1, 2)
    d = gf2_mul(c, b)
    return [
        (2, a), (1, b), (2, c), (1, b),
        (2, a), (1, b), (2, c), (1, d),
    ]


class PhaseContinuation:
    def __init__(self):
        self.dimension = 64
        self.representation = CliffordBlock(seed=0).representation
        self.relation = survivor_word()
        named_generators = factor_generators()
        self.centrality_names = [name for name, _word in named_generators]
        self.centrality_words = [
            commutator(word, self.relation)
            for _name, word in named_generators
        ]
        distinct = {}
        for word in self.centrality_words + [self.relation]:
            for _factor, matrix in word:
                distinct.setdefault(matrix_key(matrix), matrix)
        self.values = {
            key: self.representation(matrix)
            for key, matrix in distinct.items()
        }

    def export_relation_bundle(self, path):
        np.savez(
            path,
            factors=np.array([factor for factor, _matrix in self.relation]),
            matrices=np.stack([
                self.values[matrix_key(matrix)]
                for _factor, matrix in self.relation
            ]),
        )

    def factors(self, word, relative):
        adjoint = relative.conj().T
        factors = []
        for factor, matrix in word:
            value = self.values[matrix_key(matrix)]
            factors.append(
                value if factor == 1 else relative @ value @ adjoint)
        return factors

    def trace_and_gradient(self, word, relative, need_gradient):
        factors = self.factors(word, relative)
        length = len(factors)
        prefix = [np.eye(self.dimension, dtype=np.complex128)]
        for factor in factors:
            prefix.append(prefix[-1] @ factor)
        trace = float(np.trace(prefix[-1]).real / self.dimension)
        if not need_gradient:
            return trace, None
        suffix = [None] * (length + 1)
        suffix[length] = np.eye(self.dimension, dtype=np.complex128)
        for position in range(length - 1, -1, -1):
            suffix[position] = factors[position] @ suffix[position + 1]
        gradient = np.zeros(
            (self.dimension, self.dimension), dtype=np.complex128)
        for position, (factor, _matrix) in enumerate(word):
            if factor == 2:
                current = factors[position]
                rest = suffix[position + 1] @ prefix[position]
                gradient += current @ rest - rest @ current
        return trace, gradient / self.dimension

    def centrality_traces(self, relative):
        return np.array([
            self.trace_and_gradient(word, relative, False)[0]
            for word in self.centrality_words
        ])

    def objective(self, relative, phase_weight, need_gradient,
                  centrality_indices=None):
        if centrality_indices is None:
            centrality_indices = range(len(self.centrality_words))
        centrality_trace = 0.0
        gradient = np.zeros(
            (self.dimension, self.dimension), dtype=np.complex128)
        count = 0
        for index in centrality_indices:
            word = self.centrality_words[int(index)]
            value, derivative = self.trace_and_gradient(
                word, relative, need_gradient)
            centrality_trace += value
            if need_gradient:
                gradient += derivative
            count += 1
        centrality_trace /= count
        if need_gradient:
            gradient /= count
        relation_trace, relation_gradient = self.trace_and_gradient(
            self.relation, relative, need_gradient)
        score = centrality_trace - phase_weight * relation_trace
        if need_gradient:
            gradient -= phase_weight * relation_gradient
        return score, gradient

    def diagnostics(self, relative):
        centrality_traces = self.centrality_traces(relative)
        defects = np.sqrt(np.maximum(0.0, 2.0 - 2.0 * centrality_traces))
        relation_value = np.eye(self.dimension, dtype=np.complex128)
        for factor in self.factors(self.relation, relative):
            relation_value = relation_value @ factor
        relation_trace = np.trace(relation_value) / self.dimension
        worst = np.argsort(defects)[-4:][::-1]
        return {
            "centrality_rms": float(np.sqrt(np.mean(defects ** 2))),
            "centrality_max": float(defects.max()),
            "relation_trace": [
                float(relation_trace.real), float(relation_trace.imag)],
            "relation_distance_squared": float(2 - 2 * relation_trace.real),
            "worst": [
                [self.centrality_names[int(index)], float(defects[int(index)])]
                for index in worst
            ],
        }


def random_kick(relative, rng, scale):
    noise = rng.standard_normal(relative.shape)
    noise = noise + 1j * rng.standard_normal(relative.shape)
    tangent = 0.5 * (noise - noise.conj().T) / math.sqrt(relative.shape[0])
    return cayley_left(relative, tangent, scale)


def optimize(problem, initial, phase_weight, seed, iterations, report_every,
             centrality_batch, focus_every):
    rng = np.random.default_rng(seed)
    relative = initial.copy()
    if seed:
        relative = random_kick(relative, rng, 1e-3)
    best = relative.copy()
    best_score, _gradient = problem.objective(
        relative, phase_weight, False)
    started = time.time()
    print(json.dumps({
        "event": "start",
        "phase_weight": phase_weight,
        "seed": seed,
        "score": best_score,
        **problem.diagnostics(relative),
    }), flush=True)
    active = None
    for iteration in range(1, iterations + 1):
        if centrality_batch and (
                active is None or (iteration - 1) % focus_every == 0):
            active = np.argsort(problem.centrality_traces(relative))[
                :centrality_batch]
        old_score, gradient = problem.objective(
            relative, phase_weight, True, active)
        direction = -0.5 * (gradient - gradient.conj().T)
        accepted = False
        for step in (3.0, 1.0, 0.3, 0.1, 0.03, 0.01, 0.003):
            candidate = cayley_left(relative, direction, step)
            score, _gradient = problem.objective(
                candidate, phase_weight, False, active)
            if score > old_score + 1e-12:
                relative = candidate
                accepted = True
                if score > best_score:
                    best_score = score
                    best = candidate.copy()
                break
        if not accepted:
            relative = random_kick(relative, rng, 1e-4)
        if iteration % report_every == 0 or iteration == iterations:
            score, _gradient = problem.objective(
                relative, phase_weight, False)
            print(json.dumps({
                "event": "progress",
                "phase_weight": phase_weight,
                "seed": seed,
                "iteration": iteration,
                "elapsed_s": round(time.time() - started, 3),
                "score": score,
                **problem.diagnostics(relative),
            }), flush=True)
    if centrality_batch:
        score, _gradient = problem.objective(relative, phase_weight, False)
        return relative, score, problem.diagnostics(relative)
    return best, best_score, problem.diagnostics(best)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--init", required=True)
    parser.add_argument("--weights", default="0.4,0.6,1.0")
    parser.add_argument("--iterations", type=int, default=30)
    parser.add_argument("--seeds", type=int, default=1)
    parser.add_argument("--report-every", type=int, default=10)
    parser.add_argument("--centrality-batch", type=int, default=0)
    parser.add_argument("--focus-every", type=int, default=5)
    parser.add_argument("--save-prefix")
    parser.add_argument("--export-relation-bundle")
    args = parser.parse_args()
    initial = np.load(args.init)
    if initial.shape != (64, 64):
        raise ValueError("the initial relative unitary must be 64 by 64")
    problem = PhaseContinuation()
    if args.export_relation_bundle:
        problem.export_relation_bundle(args.export_relation_bundle)
    finals = []
    for phase_weight in map(float, args.weights.split(",")):
        runs = []
        for seed in range(args.seeds):
            runs.append(optimize(
                problem, initial, phase_weight, seed,
                args.iterations, args.report_every,
                args.centrality_batch, args.focus_every))
        relative, score, diagnostics = max(runs, key=lambda item: item[1])
        if args.save_prefix:
            np.save(f"{args.save_prefix}-w{phase_weight:g}.npy", relative)
        record = {
            "event": "final",
            "phase_weight": phase_weight,
            "score": score,
            **diagnostics,
        }
        finals.append(record)
        print(json.dumps(record), flush=True)
    print(json.dumps({"event": "summary", "finals": finals}), flush=True)


if __name__ == "__main__":
    main()
