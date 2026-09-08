"""One bounded CPU pilot for the four-word Leavitt 24k packet.

Run only on MSI after review. This script uses one deterministic Haar start,
k=1, at most 200 iterations, and at most 15 seconds of optimization budget.
It never loads a checkpoint. The JSON and tensor checkpoint are exploratory
numerical records, not a certificate of feasibility or a uniform gap.

Example:
    python leavitt_24k_packet_pilot.py --output /absolute/pilot.json \
        --checkpoint /absolute/pilot.pt
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import signal
import time

import torch


DIMENSION = 24
SEED = 20260908
ROW_NAMES = ("r_star", "R_v", "R_0", "R_sum")
WORD_LENGTH_BOUNDS = (166, 16, 172, 108)
SMOOTH_MAX_BETA = 8.0
CHECK_TOLERANCE = 1e-9
PACKET_ARTIFACT = (
    "research/artifacts/"
    "leavitt-24k-finite-coefficient-kernel-packet-2026-09-08.md"
)


class OptimizationBudgetExpired(Exception):
    """The one-run wall budget expired; retain the last complete best record."""


def expire_optimization(_signum, _frame):
    raise OptimizationBudgetExpired


def hs_norm(matrix):
    return float(torch.linalg.vector_norm(matrix).item() / math.sqrt(DIMENSION))


def frozen_factors():
    """Permutation columns on |a,b>, a in C3, b in C2^3."""
    cycle = torch.zeros((DIMENSION, DIMENSION), dtype=torch.complex128, device="cpu")
    flips = torch.zeros((3, DIMENSION, DIMENSION), dtype=torch.complex128, device="cpu")
    for a in range(3):
        for b in range(8):
            column = 8 * a + b
            cycle[8 * ((a + 1) % 3) + b, column] = 1
            for i in range(3):
                flips[i, 8 * a + (b ^ (1 << i)), column] = 1
    return cycle, flips


def phase_corrected_qr(matrix):
    """The Q factor with positive diagonal in R: Haar start or retraction."""
    q, r = torch.linalg.qr(matrix)
    diagonal = torch.diagonal(r)
    magnitudes = diagonal.abs()
    if not bool(torch.isfinite(magnitudes).all()) or bool((magnitudes == 0).any()):
        raise ArithmeticError("QR retraction has a nonfinite or zero diagonal")
    return q * (diagonal / magnitudes).unsqueeze(0)


def initial_haar_unitary():
    generator = torch.Generator(device="cpu")
    generator.manual_seed(SEED)
    real = torch.randn((DIMENSION, DIMENSION), generator=generator,
                       dtype=torch.float64, device="cpu")
    imag = torch.randn((DIMENSION, DIMENSION), generator=generator,
                       dtype=torch.float64, device="cpu")
    return phase_corrected_qr((real + 1j * imag) / math.sqrt(2))


def commutator(left, right):
    """Use adjoints as inverses on the unitary manifold."""
    return left @ right @ left.mH @ right.mH


def packet_rows(unitary, cycle, flips):
    """Evaluate the authenticated shared expressions; no literal word loop."""
    b1, b2, b3 = (unitary @ flips[i] @ unitary.mH for i in range(3))

    def gamma(word):
        return cycle @ word @ cycle.mH

    def gamma_squared(word):
        # C^3=I, hence Ad(C)^2=Ad(C^*).
        return cycle.mH @ word @ cycle

    d = commutator(b2, gamma(b1))
    h = gamma_squared(d)
    a = commutator(d, h)
    e = gamma(d)
    j = a @ e @ a.mH
    u = commutator(b2, gamma(b3))
    w = commutator(gamma_squared(b1), a)
    return (
        j @ cycle @ j @ cycle,
        commutator(b3, gamma(b3)) @ d.mH,
        commutator(u, w),
        commutator(commutator(b1, gamma(b2)), h)
        @ commutator(commutator(b3, gamma(b1)), gamma_squared(u)) @ a.mH,
    )


def evaluate(unitary, cycle, flips, identity):
    rows = packet_rows(unitary, cycle, flips)
    squared = torch.stack([
        (row - identity).abs().square().sum() / DIMENSION for row in rows
    ])
    # Subtracting log(4) makes the objective zero when all four rows vanish.
    objective = (
        torch.logsumexp(SMOOTH_MAX_BETA * squared, dim=0)
        - math.log(len(ROW_NAMES))
    ) / SMOOTH_MAX_BETA
    return objective, squared


def complete_record(unitary, objective, squared, iteration, elapsed):
    values = squared.detach().sqrt().tolist()
    return {
        "unitary": unitary.detach().clone(),
        "objective": float(objective.detach().item()),
        "row_residuals": dict(zip(ROW_NAMES, values)),
        "max_row_residual": max(values),
        "iteration": iteration,
        "optimization_seconds": elapsed,
    }


def scalar_record(record):
    return {key: value for key, value in record.items() if key != "unitary"}


def factor_checks(unitary, cycle, flips, identity):
    b = [unitary @ flips[i] @ unitary.mH for i in range(3)]
    frozen_traces = []
    conjugated_traces = []
    for mask in range(1, 8):
        dword = identity
        bword = identity
        for i in range(3):
            if mask & (1 << i):
                dword = dword @ flips[i]
                bword = bword @ b[i]
        frozen_traces.append(float((torch.trace(dword) / DIMENSION).abs()))
        conjugated_traces.append(float((torch.trace(bword) / DIMENSION).abs()))
    defects = {
        "U_adjoint_U": hs_norm(unitary.mH @ unitary - identity),
        "U_U_adjoint": hs_norm(unitary @ unitary.mH - identity),
        "C_cubed": hs_norm(cycle @ cycle @ cycle - identity),
        "frozen_D_involutions_max": max(
            hs_norm(flips[i] @ flips[i] - identity) for i in range(3)
        ),
        "frozen_D_commutators_max": max(
            hs_norm(flips[i] @ flips[j] - flips[j] @ flips[i])
            for i in range(3) for j in range(i + 1, 3)
        ),
        "B_involutions_max": max(hs_norm(value @ value - identity) for value in b),
        "B_self_adjoint_max": max(hs_norm(value - value.mH) for value in b),
        "B_commutators_max": max(
            hs_norm(b[i] @ b[j] - b[j] @ b[i])
            for i in range(3) for j in range(i + 1, 3)
        ),
        "C_nonidentity_normalized_trace_max": max(
            float((torch.trace(cycle) / DIMENSION).abs()),
            float((torch.trace(cycle @ cycle) / DIMENSION).abs()),
        ),
        "frozen_D_nonidentity_normalized_trace_max": max(frozen_traces),
        "B_nonidentity_normalized_trace_max": max(conjugated_traces),
        "packet_word_unitarity_max": max(
            hs_norm(row.mH @ row - identity)
            for row in packet_rows(unitary, cycle, flips)
        ),
    }
    return {
        "tolerance": CHECK_TOLERANCE,
        "defects": defects,
        "passed": all(math.isfinite(value) and value <= CHECK_TOLERANCE
                      for value in defects.values()),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New JSON report path; existing files are rejected")
    parser.add_argument("--checkpoint", type=Path, required=True,
                        help="New output .pt path containing initial/best U; never loaded")
    parser.add_argument("--iterations", type=int, default=200,
                        help="Iteration cap, from 1 through 200")
    parser.add_argument("--wall-seconds", type=float, default=15.0,
                        help="Optimization wall budget, positive and at most 15 seconds")
    args = parser.parse_args()
    if not 1 <= args.iterations <= 200:
        parser.error("--iterations must be between 1 and 200")
    if not math.isfinite(args.wall_seconds) or not 0 < args.wall_seconds <= 15:
        parser.error("--wall-seconds must be positive and at most 15")
    output = args.output.resolve()
    checkpoint = args.checkpoint.resolve()
    if output == checkpoint:
        parser.error("--output and --checkpoint must be different paths")
    if output.exists() or checkpoint.exists():
        parser.error("output paths must be new; this pilot does not overwrite or restart")

    run_started = time.monotonic()
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    cycle, flips = frozen_factors()
    identity = torch.eye(DIMENSION, dtype=torch.complex128, device="cpu")
    unitary = initial_haar_unitary()
    with torch.no_grad():
        initial_objective, initial_squared = evaluate(unitary, cycle, flips, identity)
        initial = complete_record(unitary, initial_objective, initial_squared, 0, 0.0)
        best = complete_record(unitary, initial_objective, initial_squared, 0, 0.0)
        initial_checks = factor_checks(unitary, cycle, flips, identity)
    if not initial_checks["passed"]:
        raise ArithmeticError("Initial frozen-factor/unitarity checks failed")

    history = []
    evaluations = 1
    accepted_steps = 0
    attempted_iterations = 0
    stop_reason = "iteration_cap"
    numerical_error = None
    step_size = 0.5
    setup_seconds = time.monotonic() - run_started
    optimization_started = time.monotonic()
    deadline = optimization_started + args.wall_seconds
    previous_alarm_handler = signal.signal(signal.SIGALRM, expire_optimization)
    try:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise OptimizationBudgetExpired
        signal.setitimer(signal.ITIMER_REAL, remaining)
        for iteration in range(1, args.iterations + 1):
            if time.monotonic() >= deadline:
                raise OptimizationBudgetExpired
            attempted_iterations = iteration
            point = unitary.detach().requires_grad_(True)
            objective, squared = evaluate(point, cycle, flips, identity)
            evaluations += 1
            if not bool(torch.isfinite(objective)):
                raise ArithmeticError("Nonfinite objective")
            gradient, = torch.autograd.grad(objective, point)
            # Tangent projection: grad_R F(U)=U skew(U^* grad_E F(U)).
            coordinates = point.mH @ gradient
            skew = (coordinates - coordinates.mH) / 2
            tangent = (point @ skew).detach()
            gradient_squared = float(tangent.abs().square().sum().item())
            if not math.isfinite(gradient_squared):
                raise ArithmeticError("Nonfinite tangent gradient")
            if gradient_squared <= 1e-20:
                stop_reason = "stationary_gradient"
                break

            old_objective = float(objective.detach().item())
            accepted = False
            trial_step = step_size
            for trial_number in range(1, 9):
                if time.monotonic() >= deadline:
                    raise OptimizationBudgetExpired
                with torch.no_grad():
                    trial = phase_corrected_qr(unitary - trial_step * tangent)
                    trial_objective, trial_squared = evaluate(trial, cycle, flips, identity)
                    evaluations += 1
                    if not bool(torch.isfinite(trial_objective)):
                        raise ArithmeticError("Nonfinite trial objective")
                    elapsed = time.monotonic() - optimization_started
                    candidate = complete_record(trial, trial_objective, trial_squared,
                                                iteration, elapsed)
                    # Include every evaluated unitary, even a rejected Armijo trial.
                    if candidate["max_row_residual"] < best["max_row_residual"]:
                        best = candidate
                    if candidate["objective"] <= (
                        old_objective - 1e-4 * trial_step * gradient_squared
                    ):
                        unitary = trial
                        accepted_steps += 1
                        step_size = min(1.0, trial_step * 1.25)
                        history.append({
                            **scalar_record(candidate),
                            "step_size": trial_step,
                            "line_search_trials": trial_number,
                            "tangent_gradient_frobenius": math.sqrt(gradient_squared),
                        })
                        accepted = True
                        break
                trial_step *= 0.5
            if not accepted:
                stop_reason = "line_search_stalled"
                break
    except OptimizationBudgetExpired:
        stop_reason = "wall_budget"
    except ArithmeticError as exc:
        stop_reason = "numerical_failure"
        numerical_error = str(exc)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_alarm_handler)
    optimization_seconds = time.monotonic() - optimization_started

    with torch.no_grad():
        best_checks = factor_checks(best["unitary"], cycle, flips, identity)
        verified_objective, verified_squared = evaluate(best["unitary"], cycle, flips, identity)
        replay = complete_record(best["unitary"], verified_objective, verified_squared,
                                 best["iteration"], best["optimization_seconds"])
    replay_error = max(abs(replay["row_residuals"][name] - best["row_residuals"][name])
                       for name in ROW_NAMES)
    checks_passed = (initial_checks["passed"] and best_checks["passed"]
                     and math.isfinite(replay_error) and replay_error <= CHECK_TOLERANCE)
    source_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report = {
        "schema": "leavitt-24k-packet-pilot-v1",
        "scope": "Exploratory finite-dimensional numerical pilot; not a certificate, "
                 "a feasibility proof, or a dimension-uniform lower bound.",
        "packet_artifact": PACKET_ARTIFACT,
        "script_sha256": source_sha256,
        "torch_version": str(torch.__version__),
        "device": "cpu",
        "dtype": "complex128",
        "threads": torch.get_num_threads(),
        "interop_threads": torch.get_num_interop_threads(),
        "k": 1,
        "dimension": DIMENSION,
        "seed": SEED,
        "starts": 1,
        "restart": False,
        "iteration_cap": args.iterations,
        "optimization_wall_budget_seconds": args.wall_seconds,
        "word_length_bounds": dict(zip(ROW_NAMES, WORD_LENGTH_BOUNDS)),
        "objective": "(logsumexp(8 * squared_HS_rows) - log(4)) / 8",
        "selection": "Smallest actual maximum row HS residual among all evaluated trials",
        "update": "Riemannian gradient, phase-corrected QR retraction, Armijo backtracking",
        "stop_reason": stop_reason,
        "numerical_error": numerical_error,
        "attempted_iterations": attempted_iterations,
        "accepted_steps": accepted_steps,
        "optimization_objective_evaluations_including_initial": evaluations,
        "initial": scalar_record(initial),
        "best": scalar_record(best),
        "initial_checks": initial_checks,
        "best_checks": best_checks,
        "best_residual_replay_max_error": replay_error,
        "checks_passed": checks_passed,
        "timing": {
            "setup_seconds_excluding_imports": setup_seconds,
            "optimization_seconds": optimization_seconds,
            "optimization_timer_delivery_overrun_seconds": max(
                0.0, optimization_seconds - args.wall_seconds
            ),
            "seconds_through_final_checks": time.monotonic() - run_started,
            "timer_scope": "Optimization only; a POSIX wall timer interrupts at a Python "
                           "signal boundary. Setup, final checks, and output I/O are excluded.",
        },
        "history": history,
        "checkpoint": str(checkpoint),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    checkpoint.parent.mkdir(parents=True, exist_ok=True)
    with checkpoint.open("xb") as handle:
        torch.save({
            "schema": report["schema"],
            "script_sha256": source_sha256,
            "seed": SEED,
            "initial_U": initial["unitary"],
            "best_U": best["unitary"],
            "C": cycle,
            "D": flips,
            "initial": scalar_record(initial),
            "best": scalar_record(best),
        }, handle)
    report["checkpoint_sha256"] = hashlib.sha256(checkpoint.read_bytes()).hexdigest()
    report["timing"]["seconds_through_checkpoint"] = time.monotonic() - run_started
    with output.open("x") as handle:
        json.dump(report, handle, indent=2, allow_nan=False)
        handle.write("\n")
    print(json.dumps({
        "output": str(output),
        "checkpoint": str(checkpoint),
        "stop_reason": stop_reason,
        "initial_max_row_residual": initial["max_row_residual"],
        "best_max_row_residual": best["max_row_residual"],
        "optimization_seconds": optimization_seconds,
        "checks_passed": checks_passed,
        "scope": report["scope"],
    }, allow_nan=False))
    return 0 if checks_passed and numerical_error is None else 1


if __name__ == "__main__":
    raise SystemExit(main())
