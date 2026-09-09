"""Bounded deterministic seven-cell completion pilot; MSI execution only.

Uses the separately authenticated exact prefix operations. At most 384
parameter tuples, ten seconds, and 512 rows per table; no restart. A failed
pilot excludes only its tested candidates, not arbitrary completions in V.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

import leavitt_seven_cell_exact_replay as replay
from leavitt_seven_cell_exact_replay import Prefix, cell, comm, permutation, swap, thompson_rows


# Labels are those in the proof artifact. Child suffixes deliberately change
# tail length; the finite core itself still has its seven-cell partition.
FIXED_SWAPS = (
    ("a", "c0"), ("a", "e0"), ("c", "e0"), None,
    ("a0", "c"), ("a0", "e"), ("c0", "e"),
    ("a", "c1"), ("a", "e1"), ("c", "e1"),
    ("a", "c"), ("a", "e"), ("c", "e"),
)
QUOTIENT_SWAPS = (
    ("b", "f0"), ("b", "f1"), ("b0", "f"), ("b1", "f"),
    ("b0", "f1"), ("b1", "f0"), ("b", "f"), None,
)


def transposition(spec, identity):
    return identity if spec is None else swap(cell(spec[0]), cell(spec[1]))


def paired_label(word):
    return {"b": "d", "f": "g"}[word[0]] + word[1:]


def moved_options(Y, identity):
    """All listed kappa sets are invariant under their quotient involution."""
    options = []
    for spec in QUOTIENT_SWAPS:
        h = transposition(spec, identity)
        lift = h * Y * h * Y
        flips = [("zero", identity), ("all_T", Y)]
        if spec is not None:
            u, v = spec
            support_flip = swap(cell(u), cell(paired_label(u)))
            support_flip = support_flip * swap(cell(v), cell(paired_label(v)))
            flips.extend((("support_h", support_flip), ("fixed_part_h", Y * support_flip)))
        for kappa, flip in flips:
            options.append((spec, kappa, lift * flip))
    return options


def evaluate_beta(C, Y, e, X0, Z):
    U = comm(Y, C * Z * ~C)
    P1 = comm(e, U)
    Q1 = comm(~C * Z * C, Y)
    return X0 * P1 * Q1 * P1  # The last P1 is not inverted.


def disagreement_mass(relative):
    """Exact Bernoulli a.e. moved mass; not an invariant or matrix-HS metric.

    A row with unequal prefixes fixes at most one sequence in its cylinder,
    hence a null set. Equal-prefix rows fix their whole cylinders.
    """
    return sum((Fraction(1, 1 << len(u)) for u, v in relative.rows if u != v), Fraction())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--candidates", type=int, default=256)
    parser.add_argument("--seconds", type=float, default=10.0)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("Output already exists")
    if not 1 <= args.candidates <= 384:
        parser.error("--candidates must lie in [1,384]")
    if not 0 < args.seconds <= 10:
        parser.error("--seconds must lie in (0,10]")
    started = time.monotonic()
    Prefix.deadline = started + args.seconds
    Prefix.products = Prefix.max_rows = 0
    visited = tested = duplicates = 0
    best = first = witness_checks = None
    best_mass = None
    matched = False
    seen = set()
    termination, resource_detail = "schedule_exhausted", None
    try:
        identity = Prefix((("", ""),))
        C, Y = permutation("abc", "dfe"), permutation("bd", "fg")
        d = comm(Y, C * Y * ~C)
        a = comm(d, ~C * d * C)
        e = C * d * ~C
        A, D = a * e * ~a, ~C * (a * e * ~a) * C
        p0, q0 = C * Y * ~C, comm(~C * Y * C, a)
        X0 = p0 * q0 * p0
        B0 = swap(cell("b"), cell("c0")) * swap(cell("b"), cell("c1"))
        B0 = B0 * swap(cell("e"), cell("d0")) * swap(cell("e"), cell("d1"))
        options = moved_options(Y, identity)
        stop = False
        for fixed in FIXED_SWAPS:
            v = transposition(fixed, identity)
            for quotient, kappa, moved in options:
                if visited >= args.candidates:
                    termination, stop = "candidate_cap", True
                    break
                if time.monotonic() > Prefix.deadline:
                    raise TimeoutError("Pilot wall budget exceeded")
                visited += 1
                Z = v * moved
                if Z.rows in seen:
                    duplicates += 1
                    continue
                seen.add(Z.rows)
                if not (Z ** 2).is_identity() or not comm(Z, Y).is_identity():
                    raise AssertionError("Centralizer parameter construction failed")
                beta = evaluate_beta(C, Y, e, X0, Z)
                relative = ~B0 * beta
                mass = disagreement_mass(relative)
                tested += 1
                candidate = {
                    "tested_index": tested, "fixed_swap": fixed,
                    "quotient_swap": quotient, "kappa_set": kappa,
                    "bernoulli_disagreement_mass": {"numerator": mass.numerator,
                                                     "denominator": mass.denominator},
                    "Z_table": list(Z.rows), "relative_error_table": list(relative.rows),
                }
                if first is None:
                    first = candidate
                if best_mass is None or mass < best_mass:
                    best_mass, best = mass, candidate
                if relative.is_identity():
                    matched = True
                    witness_checks = {name: row.is_identity() for name, row in {
                        "C_cube": C ** 3, "Y_square": Y ** 2, "Z_square": Z ** 2,
                        "Y_Z_commutator": comm(Y, Z), "d_square": d ** 2,
                        "anchor": (A * C) ** 2, **thompson_rows(A, beta, D),
                    }.items()}
                    if not all(witness_checks.values()):
                        raise AssertionError("Exact completion failed full row replay")
                    termination, stop = "exact_completion", True
                    break
            if stop:
                break
    except TimeoutError as error:
        termination, resource_detail = "time_cap", str(error)
    except ArithmeticError as error:
        termination, resource_detail = "table_cap", str(error)
    status = "no_completion_in_tested_candidates"
    if matched:
        status = "exact_completion" if termination == "exact_completion" else "exact_compiler_match_replay_incomplete"
    report = {
        "status": status, "termination": termination, "resource_detail": resource_detail,
        "scope": "One deterministic finite candidate list in V; no exhaustive nonexistence or matrix-gap conclusion. A completion would still not establish hyperlinearity of V.",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "prefix_replay_sha256": hashlib.sha256(Path(replay.__file__).read_bytes()).hexdigest(),
        "candidate_cap": args.candidates, "wall_budget_seconds": args.seconds,
        "prefix_table_row_cap": Prefix.row_cap, "parameter_tuples_visited": visited,
        "distinct_candidates_tested": tested, "duplicate_candidates_skipped": duplicates,
        "seconds": time.monotonic() - started, "prefix_products": Prefix.products,
        "maximum_table_rows": Prefix.max_rows, "first_candidate": first,
        "best_candidate": best, "exact_witness_checks": witness_checks,
        "exact_compiler_match": matched,
        "score_scope": "Bernoulli disagreement mass is an exact prefix-action score, not a conjugacy-invariant length or normalized-HS lower bound.",
    }
    with args.output.open("x") as stream:
        json.dump(report, stream, indent=2)
        stream.write("\n")
    print(json.dumps({k: report[k] for k in ("status", "termination", "distinct_candidates_tested",
                                           "parameter_tuples_visited", "maximum_table_rows", "seconds")},
                     separators=(",", ":")))


if __name__ == "__main__":
    main()
