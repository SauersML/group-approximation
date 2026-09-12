"""One bounded dimension-24 optimization of the actual nine-word packet.

Run only on MSI after review. Start once from the explicit four-word control,
with a deterministic small tangent perturbation. Optimize the shared nine-word
DAG for at most 200 iterations and 10 seconds, keeping both packets' residuals.
No restart, expanded-word loop, dimension sweep, or lower-bound claim.
"""

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import signal
import time

import torch

import leavitt_24k_packet_exact_control as control
import leavitt_24k_packet_pilot as pilot
import leavitt_nine_word_dag as compiler


DIMENSION = pilot.DIMENSION
PERTURBATION_SEED = 20260908
PERTURBATION_HS = 0.01
MAX_TANGENT_STEP_HS = 0.025
MONITOR_DEFINITIONS = (
    ("R_v", "comm(b_3,gamma(b_3))*~d"),
    ("R_0", "comm(u,w)"),
    ("R_sum", "comm(comm(b_1,gamma(b_2)),h)*comm(comm(b_3,gamma(b_1)),gamma2(u))*~a"),
)


def graph_pair():
    nine = compiler.compile_program()
    monitored = compiler.compile_program()
    for name, expression in MONITOR_DEFINITIONS:
        monitored.names[name] = monitored.parse(expression)
    if monitored.nodes[:len(nine.nodes)] != nine.nodes:
        raise ArithmeticError("Monitor extension changed the nine-word DAG")
    return nine, monitored


def evaluate(unitary, cycle, flips, identity, graph):
    factors = [unitary @ flips[i] @ unitary.mH for i in range(3)]
    leaves = {"c": cycle, **dict(zip(("b_1", "b_2", "b_3"), factors))}
    values = compiler.evaluate_graph(graph, leaves, lambda x, y: x @ y, lambda x: x.mH)
    rows = [values[graph.names[name]] for name in compiler.ROW_NAMES]
    squared = torch.stack([(row - identity).abs().square().sum() / DIMENSION for row in rows])
    objective = (torch.logsumexp(pilot.SMOOTH_MAX_BETA * squared, dim=0)
                 - math.log(len(rows))) / pilot.SMOOTH_MAX_BETA
    return objective, squared, values, factors


def original_rows(graph, values):
    """Extend already computed nodes; retain shared intermediates and orientation."""
    extended = list(values)
    for node in graph.nodes[len(values):]:
        if node[0] == "inv":
            value = extended[node[1]].mH
        elif node[0] == "mul":
            value = extended[node[1]] @ extended[node[2]]
        else:
            raise ArithmeticError("A monitor must reuse existing generator leaves")
        extended.append(value)
    return [extended[graph.names[name]] for name in pilot.ROW_NAMES]


def record(unitary, objective, squared, values, monitored, identity, iteration, elapsed):
    nine = squared.detach().sqrt().tolist()
    four = [pilot.hs_norm(row - identity) for row in original_rows(monitored, values)]
    return {
        "unitary": unitary.detach().clone(),
        "objective": float(objective.detach()),
        "nine_HS_residuals": dict(zip(compiler.ROW_NAMES, nine)),
        "max_nine_HS": max(nine),
        "original_four_HS_residuals": dict(zip(pilot.ROW_NAMES, four)),
        "max_original_four_HS": max(four),
        "iteration": iteration,
        "optimization_seconds": elapsed,
    }


def exact_control_unitary():
    _cycle, _flips, permutation, _b = control.explicit_factors()
    matrix = torch.zeros((DIMENSION, DIMENSION), dtype=torch.complex128, device="cpu")
    for column, row in enumerate(permutation):
        matrix[row, column] = 1
    return matrix


def perturbed_start(seed):
    generator = torch.Generator(device="cpu")
    generator.manual_seed(PERTURBATION_SEED)
    real = torch.randn((DIMENSION, DIMENSION), generator=generator, dtype=torch.float64)
    imaginary = torch.randn((DIMENSION, DIMENSION), generator=generator, dtype=torch.float64)
    noise = real + 1j * imaginary
    skew = (noise - noise.mH) / 2
    skew = skew / (torch.linalg.vector_norm(skew) / math.sqrt(DIMENSION))
    return pilot.phase_corrected_qr(seed + PERTURBATION_HS * (seed @ skew))


def gradient_diagnostics(unitary, cycle, flips, identity, graph):
    point = unitary.detach().requires_grad_(True)
    objective, _squared, _values, factors = evaluate(point, cycle, flips, identity, graph)
    gradients = torch.autograd.grad(objective, (point, *factors))
    coordinates = point.mH @ gradients[0]
    tangent = point @ ((coordinates - coordinates.mH) / 2)
    result = {
        "U_ambient_gradient_F": float(torch.linalg.vector_norm(gradients[0])),
        "U_feasible_tangent_gradient_F": float(torch.linalg.vector_norm(tangent)),
        "independent_B_ambient_gradient_F": [float(torch.linalg.vector_norm(g))
                                            for g in gradients[1:]],
        "independent_B_unitary_tangent_gradient_F": [],
        "scope": "Only the U tangent respects the simultaneous-conjugacy factor constraint; "
                 "the separate B gradients diagnose sensitivity, not allowed update directions.",
    }
    for value, gradient in zip(factors, gradients[1:]):
        coordinates = value.mH @ gradient
        projected = value @ ((coordinates - coordinates.mH) / 2)
        result["independent_B_unitary_tangent_gradient_F"].append(
            float(torch.linalg.vector_norm(projected)))
    return result


def diagnostic_record(unitary, cycle, flips, identity, graph, monitored):
    with torch.no_grad():
        objective, squared, values, _factors = evaluate(unitary, cycle, flips, identity, graph)
        result = record(unitary, objective, squared, values, monitored, identity, 0, 0.0)
        checks = pilot.factor_checks(unitary, cycle, flips, identity)
        compiled_four = original_rows(monitored, values)
        independent_four = pilot.packet_rows(unitary, cycle, flips)
        monitor_error = max(pilot.hs_norm(a - b) for a, b in zip(compiled_four, independent_four))
        word_error = max(pilot.hs_norm(values[graph.names[name]].mH
                                       @ values[graph.names[name]] - identity)
                         for name in compiler.ROW_NAMES)
        worst = max(result["nine_HS_residuals"], key=result["nine_HS_residuals"].get)
        spectra = {}
        for name in ("A", "B", "D", worst):
            eigenvalues = torch.linalg.eigvals(values[graph.names[name]])
            phases = torch.sort(torch.angle(eigenvalues)).values
            spectra[name] = {
                "ordered_phase_samples_radians": phases[[0, 6, 12, 18, 23]].tolist(),
                "eigenvalues_within_1e_minus_6_of_identity": int(((eigenvalues - 1).abs() < 1e-6).sum()),
                "max_eigenvalue_modulus_defect": float((eigenvalues.abs() - 1).abs().max()),
            }
    result.pop("unitary")
    result.update({
        "factor_checks": checks,
        "independent_original_four_replay_error": monitor_error,
        "nine_word_unitarity_error": word_error,
        "spectra": spectra,
        "gradient": gradient_diagnostics(unitary, cycle, flips, identity, graph),
        "checks_passed": checks["passed"] and math.isfinite(monitor_error)
                         and monitor_error <= pilot.CHECK_TOLERANCE
                         and math.isfinite(word_error) and word_error <= pilot.CHECK_TOLERANCE,
    })
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--iterations", type=int, default=200)
    parser.add_argument("--wall-seconds", type=float, default=10.0)
    args = parser.parse_args()
    if not 1 <= args.iterations <= 200:
        parser.error("--iterations must be between 1 and 200")
    if not math.isfinite(args.wall_seconds) or not 0 < args.wall_seconds <= 10:
        parser.error("--wall-seconds must be positive and at most 10")
    output, checkpoint = args.output.resolve(), args.checkpoint.resolve()
    if output == checkpoint or output.exists() or checkpoint.exists():
        parser.error("JSON and checkpoint must be distinct new paths; there is no restart")

    started = time.monotonic()
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    graph, monitored = graph_pair()
    artifact_bytes = compiler.ARTIFACT.read_bytes()
    source_check = compiler.source_length_check(graph, artifact_bytes.decode("utf-8"))
    native_check = compiler.exact_native_check(graph)
    if not source_check["checks_passed"] or not native_check["checks_passed"]:
        raise ArithmeticError("Current source/native nine-word authentication failed")
    cycle, flips = pilot.frozen_factors()
    identity = torch.eye(DIMENSION, dtype=torch.complex128, device="cpu")
    seed = exact_control_unitary()
    initial_unitary = perturbed_start(seed)
    seed_diagnostic = diagnostic_record(seed, cycle, flips, identity, graph, monitored)
    initial_diagnostic = diagnostic_record(initial_unitary, cycle, flips, identity, graph, monitored)
    if not seed_diagnostic["checks_passed"] or not initial_diagnostic["checks_passed"]:
        raise ArithmeticError("Seed/initial numerical checks failed")
    if seed_diagnostic["max_original_four_HS"] > 1e-12:
        raise ArithmeticError("Structured seed did not reproduce the exact four-word control")
    with torch.no_grad():
        objective, squared, values, _factors = evaluate(seed, cycle, flips, identity, graph)
        # At the parity-reflection control A=B=D=C^2. Only rho_1,rho_3,rho_5
        # fail: their matrices are C,C,C^2 respectively, all with HS defect sqrt(2).
        cycle_squared = cycle @ cycle
        expected_control = {name: cycle if name in ("rho_1", "rho_3")
                            else cycle_squared if name == "rho_5" else identity
                            for name in compiler.ROW_NAMES}
        expected_control.update({name: cycle_squared for name in ("A", "B", "D")})
        control_matrix_error = max(pilot.hs_norm(values[graph.names[name]] - expected)
                                   for name, expected in expected_control.items())
        if control_matrix_error > 1e-12:
            raise ArithmeticError("The nine-word control failed its explicit matrix identities")
        best = record(seed, objective, squared, values, monitored, identity, -1, 0.0)
        objective, squared, values, _factors = evaluate(initial_unitary, cycle, flips, identity, graph)
        initial = record(initial_unitary, objective, squared, values, monitored, identity, 0, 0.0)
        if initial["max_nine_HS"] < best["max_nine_HS"]:
            best = initial

    unitary = initial_unitary
    history = []
    attempted = accepted_steps = evaluations = 0
    step_size = 0.02
    stop_reason = "iteration_cap"
    numerical_error = None
    setup_seconds = time.monotonic() - started
    optimization_started = time.monotonic()
    deadline = optimization_started + args.wall_seconds
    previous_handler = signal.signal(signal.SIGALRM, pilot.expire_optimization)
    try:
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise pilot.OptimizationBudgetExpired
        signal.setitimer(signal.ITIMER_REAL, remaining)
        for iteration in range(1, args.iterations + 1):
            if time.monotonic() >= deadline:
                raise pilot.OptimizationBudgetExpired
            attempted = iteration
            point = unitary.detach().requires_grad_(True)
            objective, _squared, _values, _factors = evaluate(point, cycle, flips, identity, graph)
            evaluations += 1
            if not bool(torch.isfinite(objective)):
                raise ArithmeticError("Nonfinite objective")
            gradient, = torch.autograd.grad(objective, point)
            coordinates = point.mH @ gradient
            tangent = (point @ ((coordinates - coordinates.mH) / 2)).detach()
            gradient_squared = float(tangent.abs().square().sum())
            if not math.isfinite(gradient_squared):
                raise ArithmeticError("Nonfinite feasible tangent gradient")
            if gradient_squared <= 1e-20:
                stop_reason = "stationary_gradient"
                break
            old_objective = float(objective.detach())
            trial_step = min(step_size, MAX_TANGENT_STEP_HS
                             * math.sqrt(DIMENSION / gradient_squared))
            accepted = False
            for trial_number in range(1, 9):
                if time.monotonic() >= deadline:
                    raise pilot.OptimizationBudgetExpired
                with torch.no_grad():
                    trial = pilot.phase_corrected_qr(unitary - trial_step * tangent)
                    trial_objective, trial_squared, trial_values, _factors = evaluate(
                        trial, cycle, flips, identity, graph)
                    evaluations += 1
                    if not bool(torch.isfinite(trial_objective)):
                        raise ArithmeticError("Nonfinite trial objective")
                    improves_best = float(trial_squared.max().sqrt()) < best["max_nine_HS"]
                    armijo = float(trial_objective) <= (
                        old_objective - 1e-4 * trial_step * gradient_squared)
                    if improves_best or armijo:
                        candidate = record(trial, trial_objective, trial_squared, trial_values,
                                           monitored, identity, iteration,
                                           time.monotonic() - optimization_started)
                        if improves_best:
                            best = candidate
                        if armijo:
                            unitary = trial
                            accepted_steps += 1
                            step_size = min(0.1, 1.25 * trial_step)
                            history.append({**pilot.scalar_record(candidate),
                                            "step_size": trial_step,
                                            "line_search_trials": trial_number,
                                            "feasible_tangent_gradient_F": math.sqrt(gradient_squared)})
                            accepted = True
                            break
                trial_step *= 0.5
            if not accepted:
                stop_reason = "line_search_stalled"
                break
    except pilot.OptimizationBudgetExpired:
        stop_reason = "wall_budget"
    except (ArithmeticError, RuntimeError) as exc:
        stop_reason = "numerical_failure"
        numerical_error = str(exc)
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous_handler)
    optimization_seconds = time.monotonic() - optimization_started

    best_diagnostic = diagnostic_record(best["unitary"], cycle, flips, identity, graph, monitored)
    with torch.no_grad():
        objective, squared, values, _factors = evaluate(unitary, cycle, flips, identity, graph)
        final = record(unitary, objective, squared, values, monitored, identity,
                       accepted_steps, optimization_seconds)
    replay_error = max(abs(best["nine_HS_residuals"][name]
                           - best_diagnostic["nine_HS_residuals"][name]) for name in compiler.ROW_NAMES)
    replay_error = max(replay_error, max(abs(best["original_four_HS_residuals"][name]
                                            - best_diagnostic["original_four_HS_residuals"][name])
                                         for name in pilot.ROW_NAMES))
    checks_passed = best_diagnostic["checks_passed"] and replay_error <= pilot.CHECK_TOLERANCE
    sources = [Path(__file__), Path(compiler.__file__), Path(pilot.__file__), Path(control.__file__)]
    hashes = {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in sources}
    costs = Counter(node[0] for node in graph.nodes)
    report = {
        "schema": "leavitt-nine-word-structured-pilot-v1",
        "scope": "One local numerical trajectory at dimension 24. Positive residuals give no "
                 "lower bound, and small residuals require independent replay. No uniform gap claim.",
        "source_sha256": hashes,
        "artifact_sha256": hashlib.sha256(artifact_bytes).hexdigest(),
        "source_length_check": source_check,
        "native_check": native_check,
        "torch_version": str(torch.__version__),
        "device": "cpu", "dtype": "complex128", "k": 1, "dimension": DIMENSION,
        "threads": torch.get_num_threads(), "interop_threads": torch.get_num_interop_threads(),
        "starts": 1, "restart": False,
        "seed": "Parity reflection U(a,x)=((-1)^parity(x)*a,x)",
        "control_explicit_nine_matrix_replay_error": control_matrix_error,
        "control_nonidentity_nine_rows": {"rho_1": "C", "rho_3": "C", "rho_5": "C^2"},
        "perturbation_seed": PERTURBATION_SEED,
        "perturbation_tangent_HS": PERTURBATION_HS,
        "actual_initial_distance_from_control_HS": pilot.hs_norm(initial_unitary - seed),
        "objective": "(logsumexp(8*squared_nine_HS)-log(9))/8",
        "selection": "Smallest max-nine HS among control, perturbed start, and every evaluated trial",
        "update": "U skew(U* ambient_gradient), phase-corrected QR retraction, at most eight Armijo trials",
        "maximum_unretracted_tangent_step_HS": MAX_TANGENT_STEP_HS,
        "iteration_cap": args.iterations,
        "optimization_wall_budget_seconds": args.wall_seconds,
        "attempted_iterations": attempted, "accepted_steps": accepted_steps,
        "optimization_objective_evaluations": evaluations,
        "stop_reason": stop_reason, "numerical_error": numerical_error,
        "DAG_matmuls": costs["mul"], "forward_matmuls_with_factors": costs["mul"] + 6,
        "additional_monitor_matmuls_per_record": sum(node[0] == "mul"
                                                      for node in monitored.nodes[len(graph.nodes):]),
        "monitor_expressions": dict(MONITOR_DEFINITIONS),
        "control": seed_diagnostic, "initial": initial_diagnostic,
        "best": pilot.scalar_record(best), "best_diagnostics": best_diagnostic,
        "final": pilot.scalar_record(final), "history": history,
        "best_replay_error": replay_error, "checks_passed": checks_passed,
        "timing": {
            "setup_seconds_excluding_imports": setup_seconds,
            "optimization_seconds": optimization_seconds,
            "optimization_timer_delivery_overrun_seconds": max(0.0, optimization_seconds - args.wall_seconds),
            "seconds_through_final_checks": time.monotonic() - started,
            "timer_scope": "Optimization only. POSIX timer delivered at Python signal boundary; "
                           "setup, bounded diagnostics and output excluded. Use an outer process timeout.",
        },
        "next_action_criteria": [
            "A substantially lower max-nine tuple warrants exact saved-input replay and analysis of its active rows.",
            "Near-zero original four rows with persistent nine-word rows identify which added constraint breaks the control.",
            "A tiny feasible gradient or stalled line search only diagnoses this local trajectory; it is not gap evidence.",
        ],
        "checkpoint": str(checkpoint),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    checkpoint.parent.mkdir(parents=True, exist_ok=True)
    with checkpoint.open("xb") as handle:
        torch.save({"schema": report["schema"], "source_sha256": hashes,
                    "control_U": seed, "initial_U": initial_unitary,
                    "best_U": best["unitary"], "final_U": unitary.detach(),
                    "C": cycle, "D": flips, "best": pilot.scalar_record(best)}, handle)
    report["checkpoint_sha256"] = hashlib.sha256(checkpoint.read_bytes()).hexdigest()
    report["timing"]["seconds_through_checkpoint"] = time.monotonic() - started
    with output.open("x") as handle:
        json.dump(report, handle, indent=2, allow_nan=False)
        handle.write("\n")
    print(json.dumps({"output": str(output), "checkpoint": str(checkpoint),
                      "control_max_nine_HS": seed_diagnostic["max_nine_HS"],
                      "initial_max_nine_HS": initial_diagnostic["max_nine_HS"],
                      "best_max_nine_HS": best["max_nine_HS"],
                      "stop_reason": stop_reason, "optimization_seconds": optimization_seconds,
                      "checks_passed": checks_passed}, allow_nan=False))
    return 0 if checks_passed and numerical_error is None else 1


if __name__ == "__main__":
    raise SystemExit(main())
