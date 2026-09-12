"""Stage 1 of the true-criterion probe: index-15 coset deformation.

Implements the staged design of
research/artifacts/atlas-true-criterion-probe-2026-08-15.md: the ansatz
U = (I_{1344} tensor V) J with V in U(15), warm-started at the tensor flip
(V = I), objective on the DETERMINED active set (the 72 cartesian-escaping
relators of atlas-rank5-T_St.json) with a satisfied-relator control slice.

Two deliberate choices, per the design document:

* the loss uses the RESIDUAL estimator  E ||(pi(s) - I) v||^2 / (d m)
  (unbiased for the normalized defect^2, variance -> 0 at the optimum),
  NOT a Hutchinson trace estimate, whose variance does not vanish in
  exactly the regime the criterion lives in;
* V is genuinely complex (U(15) via expm of a skew-Hermitian parameter),
  not the real SO(15) of the older stabilizer-coset script.

Built-in controls (the run aborts if either fails):
  at V = I the control slice must have EXACTLY zero residual (the flip
  satisfies those relators on the nose), and the active-set defect^2
  must reproduce the landed baseline value 2.0 within estimator noise
  (atlas-true-criterion-baseline).

Group/coset machinery is imported from atlas_stabilizer_coset_search
(enumerate_group / coset ordering / permutation cache pattern); the word
loader follows atlas_true_criterion_warmstarts.load.
"""

import argparse
import json
import os
import random
import sys
import time

import numpy as np
import torch

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_two_chart_search import gf2_inv, gf2_mul  # noqa: E402
from atlas_stabilizer_coset_search import (  # noqa: E402
    enumerate_group, coset_coordinates, fixed_vector, matrix_key)

I4 = np.eye(4, dtype=np.uint8)


def load_relators(path):
    with open(path) as handle:
        payload = json.load(handle)
    out = []
    for entry in payload["relators"]:
        word = [(int(f), np.array([int(c) for c in bits],
                                  dtype=np.uint8).reshape(4, 4))
                for f, bits in entry["word"]]
        out.append((entry.get("name", "?"), word))
    return out


def factor_projections(word):
    p1, p2 = I4.copy(), I4.copy()
    for factor, matrix in word:
        if factor == 1:
            p1 = gf2_mul(p1, matrix)
        else:
            p2 = gf2_mul(p2, matrix)
    return p1, p2


class FlipCosetModel:
    """pi(s) for U = (I tensor V) J in the stabilizer-coset ordering.

    K1 syllables act by left translation; K2 syllables act by
    V . R_g . V^dagger  (J lambda J* = R, then the block deformation)."""

    def __init__(self, ordered, ordered_index, device):
        self.ordered = ordered
        self.ordered_index = ordered_index
        self.device = device
        self.cache = {}

    def permutation(self, matrix, side):
        key = (matrix_key(matrix), side)
        if key not in self.cache:
            inverse = gf2_inv(matrix)
            targets = [
                gf2_mul(matrix, value) if side == "left"
                else gf2_mul(value, inverse)
                for value in self.ordered
            ]
            self.cache[key] = torch.tensor(
                [self.ordered_index[matrix_key(value)] for value in targets],
                dtype=torch.long, device=self.device)
        return self.cache[key]

    @staticmethod
    def apply_permutation(state, permutation):
        return torch.zeros_like(state).index_copy(0, permutation, state)

    @staticmethod
    def apply_block(state, small):
        shaped = state.reshape(1344, 15, -1)
        return torch.einsum("cd,hdb->hcb", small, shaped).reshape_as(state)

    def apply_word(self, word, state, v_small):
        v_dag = v_small.conj().T
        value = state
        for factor, matrix in reversed(word):
            if factor == 1:
                value = self.apply_permutation(
                    value, self.permutation(matrix, "left"))
            else:
                value = self.apply_block(value, v_dag)
                value = self.apply_permutation(
                    value, self.permutation(matrix, "right"))
                value = self.apply_block(value, v_small)
        return value


def run(args):
    torch.set_num_threads(args.threads)
    torch.manual_seed(args.seed)
    random.seed(args.seed)
    np.random.seed(args.seed)
    started = time.time()

    words = load_relators(args.list_json)
    active, satisfied = [], []
    for name, word in words:
        p1, p2 = factor_projections(word)
        if (not np.array_equal(p1, I4)) or (not np.array_equal(p2, I4)):
            active.append((name, word))
        else:
            satisfied.append((name, word))
    if len(active) != args.expected_active:
        raise AssertionError(
            "active set is %d, expected %d" % (len(active),
                                               args.expected_active))
    control = random.sample(satisfied, min(args.control_size, len(satisfied)))

    elements, indices = enumerate_group()
    ordered, ordered_index = coset_coordinates(
        elements, indices, args.kind, fixed_vector(args.vector_bits))
    model = FlipCosetModel(ordered, ordered_index, torch.device("cpu"))

    probe = (2.0 * torch.randint(0, 2, (20160, args.probes),
                                 dtype=torch.float64) - 1.0)
    probe = probe.to(torch.complex128)
    norm = float(probe.numel())

    def defect_sq(word_list, v_small):
        vals = []
        for _name, word in word_list:
            image = model.apply_word(word, probe, v_small)
            residual = image - probe
            vals.append(torch.sum(residual.conj() * residual).real / norm)
        return torch.stack(vals)

    # ---- baseline controls at V = I ------------------------------------
    eye = torch.eye(15, dtype=torch.complex128)
    with torch.no_grad():
        base_active = defect_sq(active, eye)
        base_control = defect_sq(control, eye)
    ba, bc = float(base_active.mean()), float(base_control.max())
    print("baseline at V=I: active mean defect^2 = %.6f (expect 2.0), "
          "control max = %.3e (expect 0)" % (ba, bc))
    if bc > 1e-18:
        raise AssertionError("control slice not exactly satisfied at the "
                             "flip -- coset model is wrong")
    if abs(ba - 2.0) > 4.0 / (args.probes ** 0.5):
        raise AssertionError("active baseline %.6f deviates from the landed "
                             "value 2.0 beyond estimator noise" % ba)

    # ---- optimization ---------------------------------------------------
    param = torch.randn(15, 15, dtype=torch.complex128) * args.initial_scale
    param.requires_grad_()
    optimizer = torch.optim.Adam([param], lr=args.learning_rate)
    history = []
    best = float("inf")
    n_act, n_ctl = len(active), max(1, len(control))
    for iteration in range(args.iterations + 1):
        optimizer.zero_grad()
        # Per-word backward with immediate graph release: the escapee
        # words run to ~139 syllables, and retaining every intermediate
        # across 144 words OOMs at tens of GB.  Gradients accumulate in
        # `param` across the per-word calls; one optimizer step follows.
        act_vals, ctl_vals = [], []
        for kind, word_list, vals, weight in (
                ("active", active, act_vals, 1.0 / n_act),
                ("control", control, ctl_vals,
                 args.control_weight / n_ctl)):
            for _name, word in word_list:
                skew = param - param.conj().T
                v_small = torch.matrix_exp(skew)
                image = model.apply_word(word, probe, v_small)
                residual = image - probe
                dsq = torch.sum(residual.conj() * residual).real / norm
                vals.append(float(dsq.detach()))
                if iteration != args.iterations:
                    (weight * dsq).backward()
        act_t = torch.tensor(act_vals)
        ctl_t = torch.tensor(ctl_vals)
        value = float(act_t.mean() + args.control_weight * ctl_t.mean())
        best = min(best, value)
        if iteration % args.report_every == 0 or iteration == args.iterations:
            with torch.no_grad():
                v_now = torch.matrix_exp(param - param.conj().T)
                uerr = float(torch.linalg.norm(
                    v_now.conj().T @ v_now - eye))
            rec = {
                "iteration": iteration,
                "loss": value,
                "best_loss": best,
                "active_mean_defect_sq": float(act_t.mean()),
                "active_max_defect_sq": float(act_t.max()),
                "control_mean_defect_sq": float(ctl_t.mean()),
                "unitarity_error": uerr,
                "elapsed_s": round(time.time() - started, 1),
            }
            history.append(rec)
            print(json.dumps(rec), flush=True)
        if iteration != args.iterations:
            optimizer.step()

    out = {
        "stage": 1,
        "ansatz": "(I_1344 tensor V) J, V in U(15), complex",
        "estimator": "residual, m=%d" % args.probes,
        "kind": args.kind,
        "vector_bits": args.vector_bits,
        "active": len(active),
        "control": len(control),
        "flip_baseline_active_mean_defect_sq": ba,
        "iterations": args.iterations,
        "learning_rate": args.learning_rate,
        "seed": args.seed,
        "history": history,
        "elapsed_s": round(time.time() - started, 1),
    }
    with open(args.out, "w") as handle:
        json.dump(out, handle, indent=1)
    print("wrote", args.out)
    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("list_json")
    parser.add_argument("--kind", default="point",
                        choices=("point", "hyperplane"))
    parser.add_argument("--vector-bits", type=int, default=1)
    parser.add_argument("--expected-active", type=int, default=72)
    parser.add_argument("--control-size", type=int, default=72)
    parser.add_argument("--control-weight", type=float, default=1.0)
    parser.add_argument("--probes", type=int, default=32)
    parser.add_argument("--iterations", type=int, default=300)
    parser.add_argument("--learning-rate", type=float, default=3e-3)
    parser.add_argument("--initial-scale", type=float, default=1e-3)
    parser.add_argument("--report-every", type=int, default=10)
    parser.add_argument("--threads", type=int, default=16)
    parser.add_argument("--seed", type=int, default=7)
    parser.add_argument("--out", default="atlas-stage1-result.json")
    return run(parser.parse_args())


if __name__ == "__main__":
    sys.exit(main())
