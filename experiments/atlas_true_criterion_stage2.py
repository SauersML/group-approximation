"""Stage 2 of the true-criterion probe: unrestricted deformation around the flip.

Per research/artifacts/atlas-true-criterion-probe-2026-08-15.md §(d):
ansatz U = W · J with W ∈ U(20160) dense (so K2 syllables act by
W R_g W†), warm-started at W = I (the tensor flip), objective on the
determined 72-word active set with a satisfied-relator control slice.
Residual estimator; per-word backward; QR retraction to the unitary
group each step.  Evidence and structure discovery only — never proof:
monomial drift is a recorded descent trap (TF6/7), and the recorded
no-gos (atlas-stabilizer-commutant-no-go) kill every stabilizer-
commuting W, so a genuine move must be none of those shapes.  The run
periodically reports structure diagnostics: distance of W from the
monomial sector and from block-diagonality against the index-15 coset
blocks.
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


class FlipDenseModel:
    """pi(s) for U = W J: K1 -> left translations, K2 -> W R_g W^dagger."""

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

    def apply_word(self, word, state, w_mat):
        w_dag = None if w_mat is None else w_mat.conj().T
        value = state
        for factor, matrix in reversed(word):
            if factor == 1:
                value = self.apply_permutation(
                    value, self.permutation(matrix, "left"))
            else:
                if w_dag is not None:
                    value = w_dag @ value
                value = self.apply_permutation(
                    value, self.permutation(matrix, "right"))
                if w_mat is not None:
                    value = w_mat @ value
        return value


def block_diag_distance(w, blocks=1344, dim=15):
    """Normalized HS distance of W from its block-diagonal part."""
    with torch.no_grad():
        wb = w.reshape(blocks, dim, blocks, dim)
        diag = torch.zeros_like(w)
        idx = torch.arange(blocks, device=w.device)
        db = wb[idx, :, idx, :]
        diag = diag.reshape(blocks, dim, blocks, dim)
        diag[idx, :, idx, :] = db
        diag = diag.reshape_as(w)
        return float(torch.linalg.norm(w - diag) / (w.shape[0] ** 0.5))


def monomial_distance(w):
    """Normalized HS distance of |W| from a permutation profile: 1 minus
    the mean of the per-row maxima of |W| (0 for a monomial matrix)."""
    with torch.no_grad():
        return float(1.0 - w.abs().max(dim=1).values.mean())


def run(args):
    dev = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    torch.manual_seed(args.seed)
    random.seed(args.seed)
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
        raise AssertionError("active %d != expected %d"
                             % (len(active), args.expected_active))
    control = random.sample(satisfied, min(args.control_size, len(satisfied)))

    elements, indices = enumerate_group()
    ordered, ordered_index = coset_coordinates(
        elements, indices, "point", fixed_vector(1))
    model = FlipDenseModel(ordered, ordered_index, dev)

    n = 20160

    def draw_probe():
        p = (2.0 * torch.randint(0, 2, (n, args.probes),
                                 dtype=torch.float32) - 1.0)
        return p.to(torch.complex64).to(dev)

    # resampled every iteration: with a FIXED probe set the estimator
    # becomes the objective and the optimizer learns identity-on-the-
    # probe-subspace instead of operator proximity (observed: active
    # mean 2.0 -> 1.32 while control 0.003 -> 0.65 by iteration 5)
    probe = draw_probe()
    norm = float(probe.numel())

    def polar_retract(x, steps=4):
        """Newton-Schulz iteration to the nearest unitary, pure GEMMs.
        Note the QR retraction was NEVER broken: LAPACK/cusolver QR of a
        near-identity input returns Q = -(near I), so the warm start
        lives at the gauge copy -I (a global phase cancels in W R W*),
        and w_minus_identity = 2.0 is that gauge, not damage.  Polar is
        kept as the geometrically cleaner retraction; the honest drift
        diagnostic is the gauge-invariant one below."""
        for _ in range(steps):
            x = 1.5 * x - 0.5 * (x @ (x.conj().T @ x))
        return x

    w_mat = torch.eye(n, dtype=torch.complex64, device=dev)
    w_mat += args.initial_scale * (
        torch.randn(n, n, dtype=torch.complex64, device=dev)
        - torch.randn(n, n, dtype=torch.complex64, device=dev).conj().T)
    with torch.no_grad():
        w_mat = polar_retract(w_mat)
    w_mat.requires_grad_()
    optimizer = torch.optim.Adam([w_mat], lr=args.learning_rate)

    def defects(word_list, need_grad, weight, w_override="use"):
        w_use = w_mat if w_override == "use" else w_override
        vals = []
        for _name, word in word_list:
            image = model.apply_word(word, probe, w_use)
            residual = image - probe
            dsq = torch.sum(residual.conj() * residual).real / norm
            vals.append(float(dsq.detach()))
            if need_grad:
                (weight * dsq).backward()
        return vals

    # baseline gate at the exact flip (identity fast-path, no matmuls)
    with torch.no_grad():
        base_a = defects(active, False, 0, w_override=None)
        base_c = defects(control, False, 0, w_override=None)
    ba = float(np.mean(base_a))
    bc = float(np.max(base_c)) if base_c else 0.0
    print("baseline at W=I: active mean defect^2 = %.6f (expect ~2.0), "
          "control max = %.3e" % (ba, bc), flush=True)
    if bc > 1e-6 or abs(ba - 2.0) > 6.0 / (args.probes ** 0.5):
        raise AssertionError("baseline gate failed")

    history = []
    best = float("inf")
    n_act, n_ctl = len(active), max(1, len(control))
    for iteration in range(args.iterations + 1):
        optimizer.zero_grad(set_to_none=True)
        probe = draw_probe()  # W depends only on PAST samples: unbiased
        train = iteration != args.iterations
        act_vals = defects(active, train, 1.0 / n_act)
        ctl_vals = defects(control, train,
                           args.control_weight / n_ctl)
        value = float(np.mean(act_vals)
                      + args.control_weight * np.mean(ctl_vals))
        best = min(best, value)
        gnorm = 0.0
        if train:
            # ||grad|| at iteration 0 tests full stationarity of the flip
            # (slice-stationarity is proved; the full tangent space is open)
            if w_mat.grad is not None:
                gnorm = float(torch.linalg.norm(w_mat.grad))
            optimizer.step()
            # free the 3 GiB gradient before the retraction's temporaries
            optimizer.zero_grad(set_to_none=True)
            with torch.no_grad():
                fresh = polar_retract(w_mat.detach())
                w_mat.copy_(fresh)
                del fresh
        if iteration % args.report_every == 0 or iteration == args.iterations:
            rec = {
                "iteration": iteration,
                "loss": value,
                "best_loss": best,
                "active_mean_defect_sq": float(np.mean(act_vals)),
                "active_max_defect_sq": float(np.max(act_vals)),
                "control_mean_defect_sq": float(np.mean(ctl_vals)),
                "grad_norm": gnorm,
                "w_minus_identity": float(torch.linalg.norm(
                    w_mat.detach()
                    - torch.eye(n, dtype=w_mat.dtype, device=dev))
                    / (n ** 0.5)),
                "unitarity_defect": float(torch.linalg.norm(
                    w_mat.detach().conj().T @ w_mat.detach()
                    - torch.eye(n, dtype=w_mat.dtype, device=dev))
                    / (n ** 0.5)),
                # gauge-invariant distance^2 to the flip manifold's
                # scalar copies: min_theta ||W - e^{i theta} I||^2 / n
                "gauge_distance_sq": float(
                    2.0 - 2.0 * torch.diagonal(w_mat.detach())
                    .sum().abs().item() / n),
                "block_diag_distance": block_diag_distance(w_mat.detach()),
                "monomial_distance": monomial_distance(w_mat.detach()),
                "elapsed_s": round(time.time() - started, 1),
            }
            history.append(rec)
            print(json.dumps(rec), flush=True)

    out = {"stage": 2, "ansatz": "U = W J, W in U(20160) dense complex64",
           "estimator": "residual m=%d" % args.probes,
           "active": n_act, "control": n_ctl,
           "baseline_active_mean": ba,
           "iterations": args.iterations,
           "learning_rate": args.learning_rate, "seed": args.seed,
           "history": history,
           "elapsed_s": round(time.time() - started, 1)}
    with open(args.out, "w") as handle:
        json.dump(out, handle, indent=1)
    print("wrote", args.out, flush=True)
    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("list_json")
    parser.add_argument("--expected-active", type=int, default=72)
    parser.add_argument("--control-size", type=int, default=72)
    parser.add_argument("--control-weight", type=float, default=1.0)
    parser.add_argument("--probes", type=int, default=8)
    parser.add_argument("--iterations", type=int, default=250)
    parser.add_argument("--learning-rate", type=float, default=2e-4)
    parser.add_argument("--initial-scale", type=float, default=1e-4)
    parser.add_argument("--report-every", type=int, default=10)
    parser.add_argument("--seed", type=int, default=11)
    parser.add_argument("--out", default="atlas-stage2-result.json")
    return run(parser.parse_args())


if __name__ == "__main__":
    sys.exit(main())
