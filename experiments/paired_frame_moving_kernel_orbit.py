#!/usr/bin/env python3
"""Exact orbit audit for the paired-frame relation kernel over F_2[x].

We apply the degree-growing block transporter T=diag(T2,T2), where
T2=[[1+x^2,x],[x,1]], to the three-dimensional relation kernel K0 in
wedge^2(F_2^4).  Polynomial ranks are computed over the fraction field
F_2(x), with no numerical specialization.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import reduce

from paired_frame_kernel_polynomial_stabilizer import (
    ONE,
    X,
    PolyMatrix4,
    identity_poly,
    matrix_mul,
    poly_mul,
    wedge_image_poly,
)
from schur_packet_paired_commutant_frame import (
    COEFFICIENT_MINUS,
    COEFFICIENT_PLUS,
    FORBIDDEN,
    MINUS_WORDS,
    PAIRS,
    PLUS_WORDS,
    evaluated_frame_form,
    rank_f2,
    relation_kernel,
    symbolic_commutator_columns,
)


def poly_divmod(numerator: int, denominator: int) -> tuple[int, int]:
    if denominator == 0:
        raise ZeroDivisionError
    quotient = 0
    remainder = numerator
    denominator_degree = denominator.bit_length() - 1
    while remainder and remainder.bit_length() - 1 >= denominator_degree:
        shift = remainder.bit_length() - 1 - denominator_degree
        quotient ^= 1 << shift
        remainder ^= denominator << shift
    return quotient, remainder


def poly_gcd(left: int, right: int) -> int:
    while right:
        _, remainder = poly_divmod(left, right)
        left, right = right, remainder
    return left


@dataclass(frozen=True)
class Fraction:
    numerator: int
    denominator: int = ONE

    def __post_init__(self) -> None:
        if self.denominator == 0:
            raise ZeroDivisionError
        common = poly_gcd(self.numerator, self.denominator)
        if common not in (0, ONE):
            reduced_numerator, remainder_numerator = poly_divmod(self.numerator, common)
            reduced_denominator, remainder_denominator = poly_divmod(self.denominator, common)
            assert remainder_numerator == remainder_denominator == 0
            object.__setattr__(self, "numerator", reduced_numerator)
            object.__setattr__(self, "denominator", reduced_denominator)

    def __bool__(self) -> bool:
        return self.numerator != 0

    def __add__(self, other: "Fraction") -> "Fraction":
        return Fraction(
            poly_mul(self.numerator, other.denominator)
            ^ poly_mul(other.numerator, self.denominator),
            poly_mul(self.denominator, other.denominator),
        )

    def __mul__(self, other: "Fraction") -> "Fraction":
        return Fraction(
            poly_mul(self.numerator, other.numerator),
            poly_mul(self.denominator, other.denominator),
        )

    def inverse(self) -> "Fraction":
        if not self:
            raise ZeroDivisionError
        return Fraction(self.denominator, self.numerator)


def fraction_rank(rows: list[tuple[int, ...]]) -> int:
    work = [[Fraction(entry) for entry in row] for row in rows]
    pivot_row = 0
    if not work:
        return 0
    for column in range(len(work[0])):
        pivot = next((row for row in range(pivot_row, len(work)) if work[row][column]), None)
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        inverse = work[pivot_row][column].inverse()
        work[pivot_row] = [entry * inverse for entry in work[pivot_row]]
        for row in range(len(work)):
            if row == pivot_row or not work[row][column]:
                continue
            factor = work[row][column]
            work[row] = [
                entry + factor * pivot_entry
                for entry, pivot_entry in zip(work[row], work[pivot_row])
            ]
        pivot_row += 1
    return pivot_row


def kernel_basis() -> tuple[tuple[int, ...], ...]:
    kernel = relation_kernel(symbolic_commutator_columns(PLUS_WORDS))
    basis: list[tuple[int, ...]] = []
    for vector in sorted(kernel):
        if vector == (0,) * 6:
            continue
        if rank_f2([*basis, vector]) > len(basis):
            basis.append(vector)
    assert len(basis) == 3
    return tuple(basis)


def block_transporter() -> PolyMatrix4:
    forward = [list(row) for row in identity_poly()]
    opposite = [list(row) for row in identity_poly()]
    forward[0][1] = forward[2][3] = X
    opposite[1][0] = opposite[3][2] = X
    return matrix_mul(
        tuple(tuple(row) for row in forward),  # type: ignore[arg-type]
        tuple(tuple(row) for row in opposite),  # type: ignore[arg-type]
    )


def block_inverse_transporter() -> PolyMatrix4:
    """Inverse of the block transporter, with two identical S^-1 blocks."""
    return (
        (ONE, X, 0, 0),
        (X, ONE ^ poly_mul(X, X), 0, 0),
        (0, 0, ONE, X),
        (0, 0, X, ONE ^ poly_mul(X, X)),
    )


def move_relation(matrix: PolyMatrix4, relation: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        reduce(
            int.__xor__,
            (
                wedge_image_poly(matrix, PAIRS[index])[coordinate]
                for index, bit in enumerate(relation)
                if bit
            ),
            0,
        )
        for coordinate in range(6)
    )


def degree_profile(vector: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(entry.bit_length() - 1 for entry in vector)


def wedge_covector(form: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    return tuple(form[left][right] for left, right in PAIRS)


def audit(depth: int = 48) -> None:
    basis = kernel_basis()
    assert basis == (
        (0, 0, 0, 0, 0, 1),
        (0, 0, 0, 0, 1, 0),
        (1, 0, 0, 0, 0, 0),
    )
    transfer = block_transporter()
    hard_covector = wedge_covector(
        evaluated_frame_form(FORBIDDEN, COEFFICIENT_PLUS, PLUS_WORDS)
    )
    reverse_covector = wedge_covector(
        evaluated_frame_form((0, 1, 1), COEFFICIENT_MINUS, MINUS_WORDS)
    )
    stationary_minus_covector = wedge_covector(
        evaluated_frame_form(FORBIDDEN, COEFFICIENT_MINUS, MINUS_WORDS)
    )
    assert hard_covector == reverse_covector == (0, 1, 0, 0, 0, 0)
    assert stationary_minus_covector == (0,) * 6
    power = identity_poly()
    orbit = []
    for n in range(depth):
        moved = tuple(move_relation(power, relation) for relation in basis)
        assert fraction_rank(list(moved)) == 3
        expected_moving_degrees = (
            (-1, -1, -1, -1, 0, -1)
            if n == 0
            else (-1, 4 * n - 2, 4 * n - 3, 4 * n - 3, 4 * n - 4, -1)
        )
        assert degree_profile(moved[1]) == expected_moving_degrees
        curvature = reduce(
            int.__xor__,
            (poly_mul(left, right) for left, right in zip(hard_covector, moved[1])),
            0,
        )
        if n == 0:
            assert curvature == 0
        else:
            assert curvature.bit_length() - 1 == 4 * n - 2
        orbit.append(moved)
        if n < 8:
            print(f"n={n} relation degrees={tuple(degree_profile(row) for row in moved)}")
        power = matrix_mul(power, transfer)

    intersection_histogram: dict[int, int] = {}
    for left in range(depth):
        for right in range(left + 1, depth):
            union_rank = fraction_rank([*orbit[left], *orbit[right]])
            intersection = 6 - union_rank
            intersection_histogram[intersection] = intersection_histogram.get(intersection, 0) + 1
    print("pairwise intersection dimensions over F_2(x):", intersection_histogram)
    assert intersection_histogram == {2: depth * (depth - 1) // 2}

    accumulated = list(orbit[0])
    union_ranks = [fraction_rank(accumulated)]
    for moved in orbit[1:]:
        accumulated.extend(moved)
        union_ranks.append(fraction_rank(accumulated))
    print("span ranks of K_0+...+K_n:", union_ranks[:12], "final", union_ranks[-1])
    assert union_ranks[0] == 3
    assert union_ranks[1] == 4
    assert all(rank == 5 for rank in union_ranks[2:])
    print("orbit structure: fixed rank 2 plus pairwise-distinct moving lines")
    print("hard covector e_02* pairs with L_n in leading degree 4n-2")
    common_annihilator = (0, 0, 1, 1, 0, 0)
    for moved in orbit:
        for relation in moved:
            pairing = reduce(
                int.__xor__,
                (poly_mul(left, right) for left, right in zip(common_annihilator, relation)),
                0,
            )
            assert pairing == 0
    assert common_annihilator != hard_covector
    print("normal closure leaves only e_03*+e_12* and kills the hard covector")


if __name__ == "__main__":
    audit()
