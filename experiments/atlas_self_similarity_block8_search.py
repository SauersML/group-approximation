"""Search the minimal 8D multiplicity block for the scalar atlas phase.

The A8 irrep W=(5,2,1) restricts to D8 as sixteen faithful two-dimensional
irreps plus eight copies of each one-dimensional character.  It restricts to
the selected V4 as sixteen copies of each character.  Dividing all
multiplicities by eight gives a canonical 8D package:

* D8: two faithful irreps and one of each linear character;
* V4: two of each character.

An exact relative unitary in this block with r=iI_8 amplifies eightfold to the
64D chart problem.  This script searches only that minimal package using the
existing CPU PyTorch installation and retains the best unitary.
"""

import argparse
import json
import time

import numpy as np
import torch


def canonical_matrices():
    x = np.array([[0, 1], [1, 0]], dtype=np.complex128)
    z = np.diag([1, -1]).astype(np.complex128)
    character_keys = ((-1, -1), (-1, 1), (1, -1), (1, 1))
    b = np.zeros((8, 8), dtype=np.complex128)
    c = np.zeros((8, 8), dtype=np.complex128)
    b[:2, :2] = x
    b[2:4, 2:4] = x
    c[:2, :2] = z
    c[2:4, 2:4] = z
    for offset, (b_sign, c_sign) in enumerate(character_keys, start=4):
        b[offset, offset] = b_sign
        c[offset, offset] = c_sign

    joint_signs = [key for key in character_keys for _copy in range(2)]
    a0 = np.diag([key[0] for key in joint_signs]).astype(np.complex128)
    e0 = np.diag([key[1] for key in joint_signs]).astype(np.complex128)
    return b, c, a0, e0


def haar_unitary(dimension, seed):
    rng = np.random.default_rng(seed)
    value = (rng.standard_normal((dimension, dimension))
             + 1j * rng.standard_normal((dimension, dimension)))
    unitary, triangular = np.linalg.qr(value)
    phases = np.diag(triangular).copy()
    phases /= np.abs(phases)
    return unitary @ np.diag(phases.conj())


def solve(base_numpy, fixed, iterations, report_every):
    b, c, a0, e0 = fixed
    base = torch.tensor(base_numpy, dtype=torch.complex128)
    b = torch.tensor(b, dtype=torch.complex128)
    c = torch.tensor(c, dtype=torch.complex128)
    a0 = torch.tensor(a0, dtype=torch.complex128)
    e0 = torch.tensor(e0, dtype=torch.complex128)
    identity = torch.eye(8, dtype=torch.complex128)
    real_parameter = torch.zeros((8, 8), requires_grad=True)
    imaginary_parameter = torch.zeros((8, 8), requires_grad=True)
    optimizer = torch.optim.LBFGS(
        [real_parameter, imaginary_parameter],
        lr=1.0,
        max_iter=iterations,
        tolerance_grad=1e-14,
        tolerance_change=1e-16,
        history_size=50,
        line_search_fn="strong_wolfe",
    )
    calls = 0

    def evaluate():
        tangent = torch.complex(
            (real_parameter - real_parameter.T) / 2,
            (imaginary_parameter + imaginary_parameter.T) / 2,
        )
        relative = torch.matrix_exp(tangent) @ base
        adjoint = relative.conj().T
        a = relative @ a0 @ adjoint
        e = relative @ e0 @ adjoint
        relation = a @ b @ e @ b @ a @ b @ e @ c @ b
        difference = relation - 1j * identity
        loss = torch.sum(torch.abs(difference) ** 2) / 8
        return loss, relative, relation

    def closure():
        nonlocal calls
        optimizer.zero_grad()
        loss, _relative, _relation = evaluate()
        loss.backward()
        calls += 1
        if calls == 1 or calls % report_every == 0:
            print(json.dumps({
                "event": "progress",
                "closure_calls": calls,
                "squared_hs_error": float(loss.detach()),
            }), flush=True)
        return loss

    optimizer.step(closure)
    with torch.no_grad():
        loss, relative, relation = evaluate()
        trace = torch.trace(relation) / 8
        return relative.cpu().numpy(), {
            "closure_calls": calls,
            "squared_hs_error": float(loss),
            "hs_error": float(torch.sqrt(loss)),
            "operator_error": float(torch.linalg.matrix_norm(
                relation - 1j * identity, ord=2)),
            "relation_trace": [float(trace.real), float(trace.imag)],
        }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--seeds", type=int, default=8)
    parser.add_argument("--iterations", type=int, default=500)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--report-every", type=int, default=250)
    parser.add_argument("--save")
    args = parser.parse_args()
    torch.set_num_threads(args.threads)
    torch.set_default_dtype(torch.float64)
    fixed = canonical_matrices()
    started = time.time()
    results = []
    for seed in range(args.seeds):
        relative, diagnostics = solve(
            haar_unitary(8, 1729 + seed), fixed,
            args.iterations, args.report_every)
        results.append((relative, diagnostics))
        print(json.dumps({
            "event": "seed_final",
            "seed": seed,
            "elapsed_s": round(time.time() - started, 3),
            **diagnostics,
        }), flush=True)
    best_relative, best = min(
        results, key=lambda item: item[1]["hs_error"])
    if args.save:
        np.save(args.save, best_relative)
    print(json.dumps({
        "event": "final",
        "seeds": args.seeds,
        "elapsed_s": round(time.time() - started, 3),
        **best,
    }), flush=True)


if __name__ == "__main__":
    main()
