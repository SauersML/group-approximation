"""Trade atlas identity constraints against a scalar C11 phase.

Every bundle word except the last is targeted at the identity.  These include
24 certified-zero classes and may include phase-centrality commutators.  The
last word is the C11 survivor with a selected nontrivial scalar target.  Only
the relative chart alignment moves.  This is a finite compatibility
diagnostic, not a proof about all of [P,R].
"""

import argparse
import json
import time

import numpy as np
import torch


class MultiRelatorProblem:
    def __init__(self, bundle_path):
        bundle = np.load(bundle_path)
        self.factors = bundle["factors"]
        self.lengths = bundle["lengths"]
        self.targets = torch.tensor(bundle["targets"], dtype=torch.complex128)
        self.matrices = torch.tensor(
            bundle["matrices"], dtype=torch.complex128)
        self.source_indices = bundle["source_indices"].tolist()
        self.labels = bundle["labels"].tolist()
        self.dimension = self.matrices.shape[-1]
        if len(self.lengths) < 25 or len(self.targets) != len(self.lengths):
            raise ValueError("malformed identity/phase constraint package")
        if len(self.labels) != len(self.lengths):
            raise ValueError("constraint labels do not match the word package")
        if self.dimension < 1:
            raise ValueError("atlas model dimension must be positive")
        self.identity = torch.eye(self.dimension, dtype=torch.complex128)

    def values(self, relative):
        adjoint = relative.conj().T
        values = []
        for word_index, length in enumerate(self.lengths):
            value = self.identity
            for position in range(int(length)):
                matrix = self.matrices[word_index, position]
                if self.factors[word_index, position] == 2:
                    matrix = relative @ matrix @ adjoint
                value = value @ matrix
            values.append(value)
        return values

    def losses(self, relative):
        values = self.values(relative)
        losses = []
        for value, target in zip(values, self.targets):
            difference = value - target * self.identity
            losses.append(torch.sum(torch.abs(difference) ** 2)
                          / self.dimension)
        return torch.stack(losses), values

    def diagnostics(self, relative):
        with torch.no_grad():
            losses, values = self.losses(relative)
            identity_errors = torch.sqrt(losses[:-1])
            phase_error = torch.sqrt(losses[-1])
            phase_trace = torch.trace(values[-1]) / self.dimension
            phase_difference = (
                values[-1] - self.targets[-1] * self.identity
            ).cpu().numpy()
            worst = torch.argsort(identity_errors, descending=True)[:5]
            return {
                "identity_constraint_rms": float(torch.sqrt(torch.mean(
                    identity_errors ** 2))),
                "identity_constraint_max": float(torch.max(identity_errors)),
                "phase_hs_error": float(phase_error),
                "phase_operator_error": float(np.linalg.norm(
                    phase_difference, ord=2)),
                "phase_trace": [
                    float(phase_trace.real), float(phase_trace.imag)],
                "worst_identity_constraints": [
                    [self.labels[int(index)],
                     float(identity_errors[int(index)])]
                    for index in worst
                ],
            }


def optimize(problem, base_numpy, phase_weight, iterations, report_every):
    base = torch.tensor(base_numpy, dtype=torch.complex128)
    real_parameter = torch.zeros(
        (problem.dimension, problem.dimension), requires_grad=True)
    imaginary_parameter = torch.zeros(
        (problem.dimension, problem.dimension), requires_grad=True)
    optimizer = torch.optim.LBFGS(
        [real_parameter, imaginary_parameter],
        lr=1.0,
        max_iter=iterations,
        tolerance_grad=1e-12,
        tolerance_change=1e-14,
        history_size=30,
        line_search_fn="strong_wolfe",
    )
    closure_calls = 0
    started = time.time()

    def relative_unitary():
        tangent = torch.complex(
            (real_parameter - real_parameter.T) / 2,
            (imaginary_parameter + imaginary_parameter.T) / 2,
        )
        return torch.matrix_exp(tangent) @ base

    def closure():
        nonlocal closure_calls
        optimizer.zero_grad()
        relative = relative_unitary()
        losses, _values = problem.losses(relative)
        loss = torch.mean(losses[:-1]) + phase_weight * losses[-1]
        loss.backward()
        closure_calls += 1
        if closure_calls == 1 or closure_calls % report_every == 0:
            print(json.dumps({
                "event": "progress",
                "phase_weight": phase_weight,
                "closure_calls": closure_calls,
                "elapsed_s": round(time.time() - started, 3),
                "objective": float(loss.detach()),
            }), flush=True)
        return loss

    optimizer.step(closure)
    with torch.no_grad():
        relative = relative_unitary()
        diagnostics = problem.diagnostics(relative)
    return relative.cpu().numpy(), closure_calls, diagnostics


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--bundle", required=True)
    parser.add_argument("--init", required=True)
    parser.add_argument("--weights", default="1,10,100")
    parser.add_argument("--iterations", type=int, default=60)
    parser.add_argument("--threads", type=int, default=4)
    parser.add_argument("--report-every", type=int, default=20)
    parser.add_argument("--save-prefix")
    args = parser.parse_args()
    torch.set_num_threads(args.threads)
    torch.set_default_dtype(torch.float64)
    problem = MultiRelatorProblem(args.bundle)
    base = np.load(args.init)
    if base.shape != (problem.dimension, problem.dimension):
        raise ValueError(
            f"initial relative unitary has shape {base.shape}, expected "
            f"({problem.dimension}, {problem.dimension})")
    results = []
    for phase_weight in map(float, args.weights.split(",")):
        relative, closure_calls, diagnostics = optimize(
            problem, base, phase_weight, args.iterations, args.report_every)
        if args.save_prefix:
            np.save(f"{args.save_prefix}-w{phase_weight:g}.npy", relative)
        record = {
            "event": "final",
            "phase_weight": phase_weight,
            "closure_calls": closure_calls,
            **diagnostics,
        }
        results.append(record)
        print(json.dumps(record), flush=True)
    print(json.dumps({"event": "summary", "results": results}), flush=True)


if __name__ == "__main__":
    main()
