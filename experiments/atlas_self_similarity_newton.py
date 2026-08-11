"""Polish the near-scalar 64D atlas relation with PyTorch L-BFGS.

This script deliberately has no Sage dependency.  The Sage-side continuation
exports the eight fixed representation matrices with
`--export-relation-bundle`; this local solver then varies a single
skew-Hermitian tangent X through U=exp(X)U_0 and minimizes

    ||r(U) - i I||_2^2.

It is a local solvability diagnostic.  A tiny floating-point residual is not
an exact proof and must be followed by rank and algebraic recognition.
"""

import argparse
import json
import time

import numpy as np
import torch


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--init", required=True)
    parser.add_argument("--bundle", required=True)
    parser.add_argument("--iterations", type=int, default=40)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--report-every", type=int, default=10)
    parser.add_argument("--save")
    args = parser.parse_args()
    torch.set_num_threads(args.threads)
    torch.set_default_dtype(torch.float64)

    base_numpy = np.load(args.init)
    bundle = np.load(args.bundle)
    factors = bundle["factors"]
    matrices = torch.tensor(bundle["matrices"], dtype=torch.complex128)
    base = torch.tensor(base_numpy, dtype=torch.complex128)
    dimension = base.shape[0]
    identity = torch.eye(dimension, dtype=torch.complex128)
    target = 1j * identity

    real_parameter = torch.zeros(
        (dimension, dimension), requires_grad=True)
    imaginary_parameter = torch.zeros(
        (dimension, dimension), requires_grad=True)
    optimizer = torch.optim.LBFGS(
        [real_parameter, imaginary_parameter],
        lr=1.0,
        max_iter=args.iterations,
        tolerance_grad=1e-13,
        tolerance_change=1e-15,
        history_size=50,
        line_search_fn="strong_wolfe",
    )
    calls = 0
    started = time.time()

    def evaluate():
        real_skew = (real_parameter - real_parameter.T) / 2
        imaginary_symmetric = (
            imaginary_parameter + imaginary_parameter.T) / 2
        tangent = torch.complex(real_skew, imaginary_symmetric)
        relative = torch.matrix_exp(tangent) @ base
        adjoint = relative.conj().T
        relation = identity
        for factor, matrix in zip(factors, matrices):
            value = matrix if factor == 1 else relative @ matrix @ adjoint
            relation = relation @ value
        difference = relation - target
        loss = torch.sum(torch.abs(difference) ** 2) / dimension
        return loss, relative, relation

    def closure():
        nonlocal calls
        optimizer.zero_grad()
        loss, _relative, _relation = evaluate()
        loss.backward()
        calls += 1
        if calls == 1 or calls % args.report_every == 0:
            print(json.dumps({
                "event": "progress",
                "closure_calls": calls,
                "elapsed_s": round(time.time() - started, 3),
                "squared_hs_error": float(loss.detach()),
            }), flush=True)
        return loss

    optimizer.step(closure)
    with torch.no_grad():
        loss, relative, relation = evaluate()
        trace = torch.trace(relation) / dimension
        operator_error = torch.linalg.matrix_norm(
            relation - target, ord=2)
        unitarity_error = torch.linalg.matrix_norm(
            relative.conj().T @ relative - identity, ord=2)
        gradient_norm = torch.sqrt(sum(
            torch.sum(parameter.grad ** 2)
            for parameter in (real_parameter, imaginary_parameter)
        ))
        result = {
            "event": "final",
            "closure_calls": calls,
            "elapsed_s": round(time.time() - started, 3),
            "squared_hs_error": float(loss),
            "hs_error": float(torch.sqrt(loss)),
            "operator_error": float(operator_error),
            "relation_trace": [float(trace.real), float(trace.imag)],
            "unitarity_operator_error": float(unitarity_error),
            "parameter_gradient_norm": float(gradient_norm),
        }
        print(json.dumps(result), flush=True)
        if args.save:
            np.save(args.save, relative.cpu().numpy())


if __name__ == "__main__":
    main()
