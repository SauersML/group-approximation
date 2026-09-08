#!/usr/bin/env python3
"""Exact examples for nonsingular equations and the unitary degree proof.

Rational phases enumerate power-map fibers; rational orthogonal matrices
check constructed noncommuting root examples. This is not an algorithm for
finding roots for arbitrary coefficients and does not prove universal KL.
The all-dimensions result is the written proof linked in the report.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from flexible_hs_metric_audit import (
    Matrix, diagonal, difference, extend, frobenius_squared, identity,
    require_unitary, transpose, word_value,
)

ROOT = Path(__file__).resolve().parents[1]
PROOF = "research/artifacts/nonsingular-equations-and-approximation-radicals.md"


def exponent_sum(word: tuple[int, ...], variable: int) -> int:
    if not isinstance(variable, int) or variable < 1:
        raise ValueError("The variable index must be a positive integer")
    if any(not isinstance(letter, int) or letter == 0 for letter in word):
        raise ValueError("A word must use nonzero signed integer indices")
    return sum(1 if letter > 0 else -1 for letter in word if abs(letter) == variable)


def nonsingular_exponent(word: tuple[int, ...], variable: int) -> int:
    m = exponent_sum(word, variable)
    if not m:
        raise ValueError("The root theorem requires nonzero exponent sum")
    return m


def inverse_word(word: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(-letter for letter in reversed(word))


def freely_reduce(word: tuple[int, ...]) -> tuple[int, ...]:
    exponent_sum(word, 1)  # Validate the signed-index encoding.
    stack = []
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def power_word(variable: int, m: int) -> tuple[int, ...]:
    if variable < 1:
        raise ValueError("The variable index must be positive")
    return ((variable if m >= 0 else -variable),) * abs(m)


def power_fiber(d: int, m: int) -> tuple[tuple[Q, ...], list[tuple[Q, ...]]]:
    """Encode diagonal unitary eigenvalues by their phases in Q/Z.

    The target has distinct eigenvalues. Every root commutes with it, so
    the written proof reduces the full matrix fiber to these diagonal roots.
    """
    if d < 1 or m == 0:
        raise ValueError("Require d >= 1 and nonzero power")
    target = tuple(Q(j + 1, d + 1) for j in range(d))
    choices = [tuple(((phase + k) / m) % 1 for k in range(abs(m)))
               for phase in target]
    return target, list(product(*choices))


def degree_case(d: int, m: int) -> dict:
    target, roots = power_fiber(d, m)
    if len(set(roots)) != abs(m) ** d:
        raise ValueError("Root count or distinctness failed")
    off_diagonal_planes = 0
    for phases in roots:
        if tuple((m * phase) % 1 for phase in phases) != target:
            raise ValueError("A phase tuple is not an exact root")
        for i in range(d):
            for j in range(i + 1, d):
                ratio_phase = (phases[j] - phases[i]) % 1
                # Both the denominator and numerator of the geometric sum
                # are nonzero: its complex multiplier cannot vanish.
                if ratio_phase == 0 or (abs(m) * ratio_phase) % 1 == 0:
                    raise ValueError("Off-diagonal regularity failed")
                off_diagonal_planes += 1
    orientation = 1 if m > 0 else (-1) ** (d * d)
    signed_count = orientation * len(roots)
    if signed_count != m ** d:
        raise ValueError("The degree must be m^d, including its sign")
    return {
        "dimension": d,
        "power": m,
        "target_phases": list(map(str, target)),
        "distinct_roots": len(roots),
        "orientation_per_root": orientation,
        "signed_count": signed_count,
        "regular_off_diagonal_planes": off_diagonal_planes,
    }


def energy(a: Matrix) -> Q:
    return frobenius_squared(difference(a, identity(len(a)))) / len(a)


def root_packet(d: int, m: int) -> tuple[tuple[Matrix, ...], tuple[int, ...]]:
    """Construct an exact root example, choosing its last coefficient.

    This deliberately does not claim to solve independently prescribed
    coefficients. A and B are involutions, and A does not commute with T.
    """
    if d not in (2, 3) or not m:
        raise ValueError("Example dimensions are 2 and 3; m must be nonzero")
    a = diagonal((1, -1) if d == 2 else (1, -1, -1))
    b = extend(((Q(0), Q(1)), (Q(1), Q(0))), d, trivial=True)
    t = extend(((Q(3, 5), Q(-4, 5)), (Q(4, 5), Q(3, 5))), d, trivial=True)
    if d == 2:
        c = ((Q(5, 13), Q(-12, 13)), (Q(12, 13), Q(5, 13)))
    else:
        c = ((Q(1), Q(0), Q(0)),
             (Q(0), Q(5, 13), Q(-12, 13)),
             (Q(0), Q(12, 13), Q(5, 13)))
    prefix = (1, 5, 2, -5, 3) + power_word(5, m)
    temporary = (a, b, c, identity(d), t)
    last = transpose(word_value(temporary, prefix))
    generators = (a, b, c, last, t)
    for matrix in generators:
        require_unitary(matrix)
    return generators, prefix + (4,)


def replay() -> dict:
    degree_cases = [degree_case(d, m)
                    for d in range(1, 5)
                    for m in (-4, -3, -2, -1, 1, 2, 3, 4)]

    packets = []
    for d, m in product((2, 3), (-3, -2, -1, 1, 2, 3)):
        generators, word = root_packet(d, m)
        if nonsingular_exponent(word, 5) != m:
            raise ValueError("Wrong exponent sum in noncommuting example")
        if word_value(generators, word) != identity(d):
            raise ValueError("Constructed root fails the equation")
        if any(word_value(generators, r) != identity(d) for r in ((1, 1), (2, 2))):
            raise ValueError("An old involution relator was changed")
        commutator = energy(word_value(generators, (1, 5, -1, -5)))
        if not commutator:
            raise ValueError("Example accidentally has commuting coefficients")
        # A false commutative simplification moves every T past the coefficients.
        commuted = (1, 2, 3, 4) + power_word(5, m)
        packets.append({
            "dimension": d,
            "exponent_sum": m,
            "word": list(word),
            "exact_equation_energy": str(energy(word_value(generators, word))),
            "marked_old_coefficient_energy": str(energy(generators[0])),
            "old_coefficient_root_commutator_energy": str(commutator),
            "falsely_commuted_word_energy": str(energy(word_value(generators, commuted))),
        })
    order_failures = sum(Q(p["falsely_commuted_word_energy"]) > 0 for p in packets)
    if not order_failures:
        raise ValueError("The examples fail to expose the noncommutative-order error")

    # Singular control: a = t^(-1) (t a t^(-1)) t in the free group.
    singular_word = (2, 1, -2)
    if exponent_sum(singular_word, 2) != 0:
        raise ValueError("The negative control should be singular")
    if freely_reduce((-2,) + singular_word + (2,)) != (1,):
        raise ValueError("Singular normal-closure identity failed")
    a = diagonal((-1, -1))
    rotation = root_packet(2, 1)[0][-1]
    trial_roots = (identity(2), a, rotation, diagonal((1, -1)))
    for t in trial_roots:
        if word_value((a, t), singular_word) != a:
            raise ValueError("Central coefficient changed under conjugation")
    if word_value((a,), (1, 1)) != identity(2) or a == identity(2):
        raise ValueError("C2 coefficient witness failed")

    # A legitimate solution map need not detect the new variable of H=C2.
    for t in (identity(1), diagonal((-1,))):
        if word_value((t,), (1, 1)) != identity(1):
            raise ValueError("C2 solution-map control failed")

    sources = ["experiments/nonsingular_equation_audit.py",
               "experiments/flexible_hs_metric_audit.py", PROOF]
    return {
        "schema_version": 1,
        "status": "pass",
        "arithmetic": "fractions.Fraction; exact rational matrices and phases in Q/Z",
        "scope": "Finite checks supporting the written proof; neither a general numerical root solver nor formal verification.",
        "universal_kervaire_laudenbach_status": "OPEN",
        "checks": {
            "power_degree_cases": len(degree_cases),
            "distinct_power_roots": sum(c["distinct_roots"] for c in degree_cases),
            "regular_off_diagonal_planes": sum(c["regular_off_diagonal_planes"] for c in degree_cases),
            "noncommuting_root_packets": len(packets),
            "false_commutative_simplifications_detected": order_failures,
            "singular_equation_trial_roots_rejected": len(trial_roots),
            "new_variable_solution_maps_compared": 2,
        },
        "degree_cases": degree_cases,
        "root_packets": packets,
        "packet_scope": "The last coefficient is chosen from the displayed root; these are reproducible exact examples, not arbitrary-coefficient existence proofs.",
        "singular_control": {
            "word": list(singular_word),
            "exponent_sum": 0,
            "free_group_identity": "a = t^(-1) w t",
            "old_relator_occurrences": 0,
            "coefficient_a_energy": str(energy(a)),
            "reason_no_root_exists": "a=-I is central, so t a t^(-1)=-I for every unitary t",
        },
        "chosen_solution_map_control": {
            "equation": "t^2=1 over the trivial coefficient group",
            "universal_relative_group": "C2",
            "root_I_kills_new_generator": True,
            "root_minus_I_detects_new_generator": True,
            "scope": "Limits faithfulness of a chosen map; does not assert C2 is non-MF.",
        },
        "source_sha256": {path: sha256((ROOT / path).read_bytes()).hexdigest() for path in sources},
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report-out", type=Path)
    parser.add_argument("--compare-report", type=Path)
    args = parser.parse_args()
    report = replay()
    if args.compare_report and json.loads(args.compare_report.read_text()) != report:
        raise ValueError("Committed report differs from the exact replay")
    result = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.report_out:
        args.report_out.write_text(result)
    print(result, end="")


if __name__ == "__main__":
    main()
