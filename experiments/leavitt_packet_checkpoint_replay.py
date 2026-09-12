"""Independent literal-word replay of one saved control/best pair; no optimizer.

MSI only after review. One CPU thread, dimension 24, ten-second replay timer;
use a 25-second outer timeout for torch startup. Existing output is rejected.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path
import signal
import time
import torch
import leavitt_nine_word_dag as dag

N = 24
NAMES = ("r_star",) + tuple(f"rho_{i}" for i in range(1, 9))
FOUR = ("r_star", "R_v", "R_0", "R_sum")
LENGTHS = (166, 164, 492, 984, 498, 4528, 7576, 7576, 9880)


def literal_words():
    """Independent signed-letter transcription; the DAG is only a comparison."""
    c, b1, b2, b3 = (1,), (2,), (3,), (4,)
    inv = lambda w: tuple(-x for x in reversed(w))
    comm = lambda x, y: x + y + inv(x) + inv(y)
    power = lambda x, y: inv(y) + x + y
    gamma = lambda x: c + x + inv(c)
    gamma2 = lambda x: inv(c) + x + c
    d = comm(b2, gamma(b1))
    h, e = gamma2(d), gamma(d)
    a = comm(d, h)
    A = a + e + inv(a)
    u, w = comm(b2, gamma(b3)), comm(gamma2(b1), a)
    p0, q0 = gamma(b2), w
    p1, q1 = comm(e, u), comm(gamma2(b3), b1)
    B, D = p0 + q0 + p0 + p1 + q1 + p1, gamma2(A)
    r = A + c + A + c
    rows = (r, A * 2, B * 3, (A + B) * 4, power(D, A + D) + inv(A),
            inv(D) + power(A, B + D + A + D + A + power(A, B + A))
            + power(A, inv(B) + D + A + D + A + power(A, inv(B) + A)),
            comm(power(A, inv(B) + D + A + D),
                 power(A, inv(B) + D + A + D + power(A, B) + power(A, inv(B) + A))),
            comm(power(A, B + D + A + D),
                 power(A, inv(B) + D + A + D + power(A, B) + power(A, inv(B) + A))),
            comm(power(A, B + D + power(A, B + D + A)),
                 power(A, B + D + A + D + power(A, B) + power(A, inv(B) + A))))
    old = (r, comm(b3, gamma(b3)) + inv(d), comm(u, w),
           comm(comm(b1, gamma(b2)), h) + comm(comm(b3, gamma(b1)), gamma2(u)) + inv(a))
    K = A + c
    L = inv(K) + inv(c) + inv(K) + inv(c)
    return rows, old, {"d": d, "L": L, "ac": a + c}


def hs(value):
    return float(torch.linalg.vector_norm(value) / math.sqrt(N))


def expired(_signum, _frame):
    raise TimeoutError("ten-second replay budget")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--pilot-report", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists() or args.output.resolve() in (args.checkpoint.resolve(), args.pilot_report.resolve()):
        parser.error("output must be new and distinct from both inputs")
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    started = time.monotonic()
    result = {"schema": "leavitt-independent-checkpoint-replay-v1", "points": {},
              "dimension": N, "torch_version": str(torch.__version__),
              "threads": torch.get_num_threads(), "interop_threads": torch.get_num_interop_threads(),
              "replay_budget_seconds": 10, "checkpoint": str(args.checkpoint),
              "pilot_report": str(args.pilot_report)}
    previous = signal.signal(signal.SIGALRM, expired)
    signal.setitimer(signal.ITIMER_REAL, 10.0)
    try:
        reference_bytes = args.pilot_report.read_bytes()
        reference = json.loads(reference_bytes)
        result["pilot_report_sha256"] = hashlib.sha256(reference_bytes).hexdigest()
        digest = hashlib.sha256(args.checkpoint.read_bytes()).hexdigest()
        if digest != reference["checkpoint_sha256"]:
            raise ArithmeticError("Checkpoint hash disagrees with the frozen pilot report")
        saved = torch.load(args.checkpoint, map_location="cpu", weights_only=True)
        C, flips = saved["C"], saved["D"]
        I = torch.eye(N, dtype=torch.complex128)
        expected_c, expected_d, expected_u = torch.zeros_like(I), torch.zeros((3, N, N), dtype=I.dtype), torch.zeros_like(I)
        for a in range(3):
            for x in range(8):
                column = 8 * a + x
                expected_c[8 * ((a + 1) % 3) + x, column] = 1
                expected_u[8 * ((-a if x.bit_count() % 2 else a) % 3) + x, column] = 1
                for bit in range(3):
                    expected_d[bit, column ^ (1 << bit), column] = 1
        frozen_ok = torch.equal(C, expected_c) and torch.equal(flips, expected_d)
        frozen_ok = frozen_ok and torch.equal(saved["control_U"], expected_u)
        if not frozen_ok:
            raise ArithmeticError("Wrong frozen factor orientation or exact control")
        rows, old, auxiliary = literal_words()
        if tuple(map(len, rows)) != LENGTHS:
            raise ArithmeticError("Independent literal lengths disagree with the native compiler")
        graph = dag.compile_program()
        with torch.no_grad():
            for label, key in (("control", "control_U"), ("best", "best_U")):
                U = saved[key].to(dtype=torch.complex128, device="cpu")
                if U.shape != (N, N) or not bool(torch.isfinite(U).all()):
                    raise ArithmeticError("Wrong shape or nonfinite saved U")
                generators = {1: C, **{i + 2: U @ flips[i] @ U.mH for i in range(3)}}
                generators.update({-i: value.mH for i, value in tuple(generators.items())})
                def evaluate(word):
                    value = I
                    for letter in word:
                        value = value @ generators[letter]
                    return value
                nine = [evaluate(word) for word in rows]
                leaves = dict(zip(("c", "b_1", "b_2", "b_3"), (generators[i] for i in range(1, 5))))
                comparison = dag.evaluate_graph(graph, leaves, lambda x, y: x @ y, lambda x: x.mH)
                four = [evaluate(word) for word in old]
                aux = {name: evaluate(word) for name, word in auxiliary.items()}
                residuals = dict(zip(NAMES, (hs(value - I) for value in nine)))
                old_residuals = dict(zip(FOUR, (hs(value - I) for value in four)))
                d2, L, R, ac = aux["d"] @ aux["d"], aux["L"], nine[0], aux["ac"]
                errors = {"U_unitarity": hs(U.mH @ U - I),
                          "literal_vs_DAG_matrices": max(hs(value - comparison[graph.names[name]]) for name, value in zip(NAMES, nine)),
                          "rho4_commutator_identity": hs(nine[4] - L @ R @ L.mH @ R.mH),
                          "j_square_conjugate_d_square": hs(nine[1] - ac @ d2 @ ac.mH),
                          "nine_word_unitarity": max(hs(value.mH @ value - I) for value in nine),
                          "nine_DAG_report_replay": max(abs(residuals[name] - reference[label]["nine_HS_residuals"][name]) for name in NAMES),
                          "four_report_replay": max(abs(old_residuals[name] - reference[label]["original_four_HS_residuals"][name]) for name in FOUR)}
                eight = {name: value for name, value in residuals.items() if name not in ("rho_1", "rho_4")}
                eight["d_squared"] = hs(d2 - I)
                e8, e9 = sum(value * value for value in eight.values()), sum(value * value for value in residuals.values())
                errors["energy_identity"] = abs(e9 - e8 - residuals["rho_4"] ** 2)
                result["points"][label] = {"nine_HS": residuals, "original_four_HS": old_residuals,
                    "eight_HS": eight, "max_eight_HS": max(eight.values()), "max_nine_HS": max(residuals.values()),
                    "sum_squared_eight_HS": e8, "sum_squared_nine_HS": e9, "errors": errors,
                    "rho4_bound_slack": 2 * residuals["r_star"] - residuals["rho_4"],
                    "checks_passed": all(math.isfinite(x) and x <= 1e-8 for x in errors.values())
                                     and residuals["rho_4"] <= 2 * residuals["r_star"] + 1e-8}
        result.update({"checkpoint_sha256": digest, "literal_lengths": dict(zip(NAMES, LENGTHS)),
                       "checks_passed": all(point["checks_passed"] for point in result["points"].values())})
    except (TimeoutError, ArithmeticError, RuntimeError) as exc:
        result.update({"checks_passed": False, "error": str(exc)})
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, previous)
    result.update({"elapsed_seconds_excluding_torch_startup": time.monotonic() - started,
                   "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "comparison_DAG_sha256": hashlib.sha256(Path(dag.__file__).read_bytes()).hexdigest(),
                   "scope": "Independent floating-point replay of saved tuples and exact-identity checks; no optimization or gap bound."})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("x") as handle:
        json.dump(result, handle, indent=2, allow_nan=False)
        handle.write("\n")
    print(json.dumps({"output": str(args.output), "checks_passed": result["checks_passed"],
                      "replay_seconds": result["elapsed_seconds_excluding_torch_startup"]}))
    return 0 if result["checks_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
