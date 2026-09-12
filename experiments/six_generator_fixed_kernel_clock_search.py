#!/usr/bin/env python3
"""Search six-generator one-jump forms with a fixed opposite-shear clock.

Fix the total K=J=- form to the standard three-qubit symplectic form.  For
every rank-four marked form J, put K=total+J.  The common edge kernel is the
annihilator of span{J,K} in wedge^2(F2^6).  A polynomial transvection
I+xE_ab preserves the scalar-extended kernel iff every coefficient of the
pulled-back two-dimensional form space remains in span{J,K}.

An opposite pair (a,b),(b,a) yields the degree-growing SL2 clock which the
four-generator paired frame cannot support.
"""
from __future__ import annotations

from itertools import product

from two_flag_mixed_router_search import N, PAIRS, Form, form_rank

ONE = 1
X = 2


def poly_mul(left: int, right: int) -> int:
    out = 0
    while right:
        low = right & -right
        out ^= left << (low.bit_length() - 1)
        right ^= low
    return out


def transvection(row: int, column: int) -> tuple[tuple[int, ...], ...]:
    matrix = [[ONE if i == j else 0 for j in range(N)] for i in range(N)]
    matrix[row][column] = X
    return tuple(tuple(line) for line in matrix)


def pulled_form_polynomials(
    form_mask: int, matrix: tuple[tuple[int, ...], ...]
) -> tuple[int, ...]:
    values = []
    for left, right in PAIRS:
        value = 0
        for bit, (i, j) in enumerate(PAIRS):
            if (form_mask >> bit) & 1:
                value ^= poly_mul(matrix[i][left], matrix[j][right])
                value ^= poly_mul(matrix[i][right], matrix[j][left])
        values.append(value)
    return tuple(values)


def coefficient_mask(polynomials: tuple[int, ...], degree: int) -> int:
    return sum(((polynomial >> degree) & 1) << bit for bit, polynomial in enumerate(polynomials))


def preserves_form_span(row: int, column: int, j_mask: int, k_mask: int) -> bool:
    span = {0, j_mask, k_mask, j_mask ^ k_mask}
    matrix = transvection(row, column)
    for form_mask in (j_mask, k_mask):
        pulled = pulled_form_polynomials(form_mask, matrix)
        maximum_degree = max(polynomial.bit_length() - 1 for polynomial in pulled)
        if any(coefficient_mask(pulled, degree) not in span for degree in range(maximum_degree + 1)):
            return False
    return True


def mask_to_form(mask: int) -> Form:
    return tuple((mask >> bit) & 1 for bit in range(len(PAIRS)))


def audit() -> None:
    total_mask = sum(
        1 << bit
        for bit, pair in enumerate(PAIRS)
        if pair in {(0, 1), (2, 3), (4, 5)}
    )
    assert form_rank(mask_to_form(total_mask)) == 6

    witnesses = []
    rank_four_count = 0
    for j_mask in range(1 << len(PAIRS)):
        if form_rank(mask_to_form(j_mask)) != 4:
            continue
        rank_four_count += 1
        k_mask = total_mask ^ j_mask
        lifts = [
            (row, column)
            for row, column in product(range(N), repeat=2)
            if row != column and preserves_form_span(row, column, j_mask, k_mask)
        ]
        opposite = sorted(
            (row, column)
            for row, column in lifts
            if row < column and (column, row) in lifts
        )
        if opposite:
            profiles = {
                (k, j): form_rank(
                    mask_to_form((k * k_mask) ^ (j * j_mask))
                )
                for k, j in product((0, 1), repeat=2)
            }
            assert profiles[(0, 1)] == 4 and profiles[(1, 1)] == 6
            witnesses.append(
                (
                    j_mask.bit_count() + k_mask.bit_count(),
                    j_mask.bit_count(),
                    j_mask,
                    k_mask,
                    tuple(lifts),
                    tuple(opposite),
                    profiles,
                )
            )

    assert rank_four_count > 0
    witnesses.sort()
    print(f"rank-four marked forms searched={rank_four_count}")
    print(f"one-jump forms with an opposite polynomial shear pair={len(witnesses)}")
    if not witnesses:
        return
    complexity, _, j_mask, k_mask, lifts, opposite, profiles = witnesses[0]
    print(f"minimum total form weight={complexity}")
    print(f"J form={mask_to_form(j_mask)}")
    print(f"K form={mask_to_form(k_mask)}")
    print(f"rank profile={profiles}")
    print(f"polynomial transvection lifts={lifts}")
    print(f"opposite pairs={opposite}")


if __name__ == "__main__":
    audit()
