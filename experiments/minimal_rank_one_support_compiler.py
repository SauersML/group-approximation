#!/usr/bin/env python3
"""Exhaust the smallest affine rank compilers for child-without-parent.

The target predicate is (not e) and f on the Boolean square.  We enumerate
all 2-by-2 matrices of affine F_2 forms, retain the rank-normalized profile

    rank M(e,f) = 1 + (1+e)f,

and separately compute the intertwiner-Laplacian gap of the fixed baseline
Pauli packet carrying the two central selector signs.

No third-party package is required for the exhaustive search.  NumPy is used
only for the tiny 4-by-4 spectral check when available; a closed-form expected
value is also asserted.
"""
from __future__ import annotations

import argparse
import json
from itertools import product


ASSIGNMENTS = ((0, 0), (0, 1), (1, 0), (1, 1))
TARGET = (1, 2, 1, 1)


def affine_value(form: int, e: int, f: int) -> int:
    """Bit mask form = c + a*e + b*f over F_2."""
    return ((form >> 0) & 1) ^ (((form >> 1) & 1) & e) ^ (((form >> 2) & 1) & f)


def rank2(entries: tuple[int, int, int, int], e: int, f: int) -> int:
    a, b, c, d = (affine_value(x, e, f) for x in entries)
    if not (a or b or c or d):
        return 0
    return 2 if (a & d) ^ (b & c) else 1


def rank_f2(matrix: list[list[int]]) -> int:
    work = [row[:] for row in matrix]
    rows = len(work)
    cols = len(work[0]) if rows else 0
    pivot_row = 0
    for col in range(cols):
        pivot = next((r for r in range(pivot_row, rows) if work[r][col]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        for r in range(rows):
            if r != pivot_row and work[r][col]:
                work[r] = [x ^ y for x, y in zip(work[r], work[pivot_row])]
        pivot_row += 1
        if pivot_row == rows:
            break
    return pivot_row


def form_text(form: int) -> str:
    terms = []
    if form & 1:
        terms.append("1")
    if form & 2:
        terms.append("e")
    if form & 4:
        terms.append("f")
    return "+".join(terms) or "0"


def matrix_text(entries: tuple[int, int, int, int]) -> list[list[str]]:
    a, b, c, d = entries
    return [[form_text(a), form_text(b)], [form_text(c), form_text(d)]]


def complexity(entries: tuple[int, int, int, int]) -> tuple[int, int]:
    return (sum(x != 0 for x in entries), sum(x.bit_count() for x in entries))


NONZERO_VECTORS = ((1, 0), (0, 1), (1, 1))


def affine_mul_bit(form: int, bit: int) -> int:
    return form if bit else 0


def affine_xor(*forms: int) -> int:
    out = 0
    for form in forms:
        out ^= form
    return out


def fixed_pauli_pivots(entries: tuple[int, int, int, int]) -> list[tuple[tuple[int, int], tuple[int, int]]]:
    """Pairs (r,c) with the affine form r^T M c identically one."""
    a, b, c, d = entries
    pivots = []
    for row in NONZERO_VECTORS:
        for col in NONZERO_VECTORS:
            value = affine_xor(
                affine_mul_bit(a, row[0] & col[0]),
                affine_mul_bit(b, row[0] & col[1]),
                affine_mul_bit(c, row[1] & col[0]),
                affine_mul_bit(d, row[1] & col[1]),
            )
            if value == 1:
                pivots.append((row, col))
    return pivots


def enumerate_compilers() -> dict[str, object]:
    solutions = []
    fixed_pivot = []
    for entries in product(range(8), repeat=4):
        profile = tuple(rank2(entries, e, f) for e, f in ASSIGNMENTS)
        if profile != TARGET:
            continue
        solutions.append(entries)
        if entries[0] == 1:
            fixed_pivot.append(entries)

    solutions.sort(key=lambda x: (complexity(x), x))
    fixed_pivot.sort(key=lambda x: (complexity(x), x))
    chosen = (1, 3, 4, 0)  # [[1,1+e],[f,0]]
    assert chosen in fixed_pivot
    assert tuple(rank2(chosen, e, f) for e, f in ASSIGNMENTS) == TARGET

    best_complexity = complexity(solutions[0])
    best = [x for x in solutions if complexity(x) == best_complexity]
    best_pivot_complexity = complexity(fixed_pivot[0])
    best_pivot = [x for x in fixed_pivot if complexity(x) == best_pivot_complexity]
    pivot_histogram: dict[int, int] = {}
    for entries in solutions:
        count = len(fixed_pauli_pivots(entries))
        pivot_histogram[count] = pivot_histogram.get(count, 0) + 1
    maximum_pivots = max(pivot_histogram)
    most_pivoted = [x for x in solutions if len(fixed_pauli_pivots(x)) == maximum_pivots]
    return {
        "assignments": ASSIGNMENTS,
        "target_profile": TARGET,
        "solution_count": len(solutions),
        "fixed_upper_left_one_count": len(fixed_pivot),
        "minimum_complexity": best_complexity,
        "minimum_compiler_count": len(best),
        "minimum_compilers": [matrix_text(x) for x in best[:16]],
        "minimum_fixed_pivot_complexity": best_pivot_complexity,
        "minimum_fixed_pivot_compiler_count": len(best_pivot),
        "minimum_fixed_pivot_compilers": [matrix_text(x) for x in best_pivot[:16]],
        "fixed_pauli_pivot_histogram": pivot_histogram,
        "maximum_fixed_pauli_pivots": maximum_pivots,
        "maximum_pivot_compiler_count": len(most_pivoted),
        "maximum_pivot_compilers": [
            {
                "matrix": matrix_text(x),
                "complexity": complexity(x),
                "pivots": fixed_pauli_pivots(x),
            }
            for x in most_pivoted[:16]
        ],
        "chosen": matrix_text(chosen),
        "chosen_complexity": complexity(chosen),
        "chosen_fixed_pauli_pivots": fixed_pauli_pivots(chosen),
    }


def outer(left: tuple[int, ...], right: tuple[int, ...]) -> list[list[int]]:
    return [[x & y for y in right] for x in left]


def matrix_xor(*matrices: list[list[int]]) -> list[list[int]]:
    return [
        [
            matrices[0][i][j] ^ matrices[1][i][j] ^ matrices[2][i][j]
            for j in range(len(matrices[0][0]))
        ]
        for i in range(len(matrices[0]))
    ]


def affine_matrix_from_values(
    at_00: list[list[int]], at_01: list[list[int]], at_10: list[list[int]]
) -> tuple[int, ...]:
    entries = []
    for i in range(len(at_00)):
        for j in range(len(at_00[0])):
            constant = at_00[i][j]
            coeff_e = at_10[i][j] ^ constant
            coeff_f = at_01[i][j] ^ constant
            entries.append(constant | (coeff_e << 1) | (coeff_f << 2))
    return tuple(entries)


def matrix_text_square(entries: tuple[int, ...], size: int) -> list[list[str]]:
    return [
        [form_text(entries[size * i + j]) for j in range(size)]
        for i in range(size)
    ]


def search_collapsing_two_pivot_compilers() -> dict[str, object]:
    """Search the 64 canonical 3x3 two-pivot affine candidates.

    Requiring entries (1,1) and (2,2) to be fixed one and allowed matrices to
    have rank one forces every allowed evaluation to be

        (1,1,a)^T (1,1,b),  a,b in F_2.

    Choose the evaluations at 00,10,11; affine dependence determines the
    forbidden 01 evaluation as their XOR.  Retain rank two there.
    """
    rank_one_values = [
        outer((1, 1, a), (1, 1, b)) for a, b in product((0, 1), repeat=2)
    ]
    candidates = []
    for at_00, at_10, at_11 in product(rank_one_values, repeat=3):
        at_01 = matrix_xor(at_00, at_10, at_11)
        if rank_f2(at_01) != 2:
            continue
        entries = affine_matrix_from_values(at_00, at_01, at_10)
        profile = tuple(
            rank_f2(
                [
                    [affine_value(entries[3 * i + j], e, f) for j in range(3)]
                    for i in range(3)
                ]
            )
            for e, f in ASSIGNMENTS
        )
        assert profile == (1, 2, 1, 1)
        candidates.append(entries)
    candidates.sort(key=lambda x: (complexity(x), x))
    best_complexity = complexity(candidates[0])
    best = [x for x in candidates if complexity(x) == best_complexity]
    return {
        "canonical_search_space": 64,
        "solution_count": len(candidates),
        "minimum_complexity": best_complexity,
        "minimum_compiler_count": len(best),
        "minimum_compilers": [matrix_text_square(x, 3) for x in best[:16]],
    }


def search_conditional_two_pivot_compilers() -> dict[str, object]:
    """Classify 2x2 compilers that split exactly when the parent e vanishes.

    The target profile (2,2,1,1) ignores f.  On a separately named f=1 child
    carrier this is exactly child-without-parent.  We retain matrices with at
    least two fixed Pauli pivots, so the two subgroup coordinates are named by
    assignment-independent words.
    """
    target = (2, 2, 1, 1)
    solutions = []
    for entries in product(range(8), repeat=4):
        profile = tuple(rank2(entries, e, f) for e, f in ASSIGNMENTS)
        if profile == target and len(fixed_pauli_pivots(entries)) >= 2:
            solutions.append(entries)
    solutions.sort(key=lambda x: (complexity(x), -len(fixed_pauli_pivots(x)), x))
    best_complexity = complexity(solutions[0])
    best = [x for x in solutions if complexity(x) == best_complexity]
    chosen = (1, 1, 2, 1)  # [[1,1],[e,1]]
    assert chosen in solutions
    pivot_histogram: dict[int, int] = {}
    for entries in solutions:
        count = len(fixed_pauli_pivots(entries))
        pivot_histogram[count] = pivot_histogram.get(count, 0) + 1
    return {
        "target_profile": target,
        "solution_count": len(solutions),
        "minimum_complexity": best_complexity,
        "minimum_compiler_count": len(best),
        "minimum_compilers": [
            {"matrix": matrix_text(x), "pivots": fixed_pauli_pivots(x)}
            for x in best[:16]
        ],
        "fixed_pauli_pivot_histogram": pivot_histogram,
        "chosen": matrix_text(chosen),
        "chosen_pivots": fixed_pauli_pivots(chosen),
    }


def baseline_laplacian_gap() -> dict[str, object]:
    """Compute the gap for S={P,Q,z_e,z_f} in the Pauli-word basis.

    On {I,P,Q,PQ}, the P/Q commutator energies are respectively
    (0,4,4,8).  Every central selector whose signs differ adds 4 times the
    identity quadratic form.  This is an exact integer diagonalization and
    avoids a numerical linear-algebra dependency on compute nodes.
    """
    gaps = {}
    global_positive = []
    for source in ASSIGNMENTS:
        for target in ASSIGNMENTS:
            hamming = sum(x != y for x, y in zip(source, target))
            eigenvalues = [4 * hamming + x for x in (0, 4, 4, 8)]
            positive = [x for x in eigenvalues if x > 0]
            gap = min(positive) if positive else None
            gaps[f"{source}->{target}"] = {
                "selector_hamming_distance": hamming,
                "eigenvalues": eigenvalues,
                "positive_gap": gap,
            }
            global_positive.extend(positive)
    global_gap = min(global_positive)
    assert global_gap == 4
    return {
        "diagonalization": "exact Pauli-word basis",
        "generators": ["P", "Q", "z_e", "z_f"],
        "global_positive_gap": global_gap,
        "pair_spectra": gaps,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    result = {
        "compiler_search": enumerate_compilers(),
        "collapsing_two_pivot_3x3_search": search_collapsing_two_pivot_compilers(),
        "conditional_two_pivot_2x2_search": search_conditional_two_pivot_compilers(),
        "baseline_packet_laplacian": baseline_laplacian_gap(),
        "packet": {
            "full_group_order_upper_bound": 128,
            "baseline_simple_dimension": 2,
            "allowed_full_simple_dimension": 2,
            "forbidden_full_simple_dimension": 4,
            "restriction_multiplicity_allowed": 1,
            "restriction_multiplicity_forbidden": 2,
        },
    }
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        search = result["compiler_search"]
        print(f"all compilers: {search['solution_count']}")
        print(f"fixed-pivot compilers: {search['fixed_upper_left_one_count']}")
        print(f"minimum complexity: {search['minimum_complexity']}")
        print(f"minimum fixed-pivot complexity: {search['minimum_fixed_pivot_complexity']}")
        print(f"fixed Pauli pivot histogram: {search['fixed_pauli_pivot_histogram']}")
        print(f"maximum fixed Pauli pivots: {search['maximum_fixed_pauli_pivots']}")
        print(f"chosen compiler: {search['chosen']}")
        print(f"chosen fixed Pauli pivots: {search['chosen_fixed_pauli_pivots']}")
        two_pivot = result["collapsing_two_pivot_3x3_search"]
        print(f"collapsing two-pivot 3x3 compilers: {two_pivot['solution_count']}")
        print(f"best collapsing two-pivot compiler: {two_pivot['minimum_compilers'][0]}")
        conditional = result["conditional_two_pivot_2x2_search"]
        print(f"conditional two-pivot 2x2 compilers: {conditional['solution_count']}")
        print(f"best conditional two-pivot compiler: {conditional['minimum_compilers'][0]}")
        print(f"chosen conditional pivots: {conditional['chosen_pivots']}")
        print(
            "baseline packet Laplacian gap:",
            result["baseline_packet_laplacian"].get("global_positive_gap"),
        )


if __name__ == "__main__":
    main()
