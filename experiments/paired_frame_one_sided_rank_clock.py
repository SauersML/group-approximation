#!/usr/bin/env python3
"""Exact one-sided rank clock for the paired Schur packet over F_2[x].

Only the source copy of the paired frame is transported by T^n; the
coefficient copy is held fixed.  Consequently the relation kernel of the
combined six-coordinate central commutator map is K_n intersect K_0, not a
global quotient by the span of all K_n.  This script verifies the resulting
single rank jump and computes the gcd of its maximal minors.
"""
from __future__ import annotations

from functools import reduce
from itertools import combinations, permutations

from paired_frame_kernel_polynomial_stabilizer import (
    ONE,
    identity_poly,
    matrix_mul,
    poly_mul,
    wedge_image_poly,
)
from paired_frame_moving_kernel_orbit import (
    block_inverse_transporter,
    fraction_rank,
    poly_gcd,
)
from schur_packet_paired_commutant_frame import (
    PAIRS,
    PLUS_WORDS,
    symbolic_commutator_columns,
)


PolyMatrix = tuple[tuple[int, ...], ...]


def poly_add_many(values) -> int:
    return reduce(int.__xor__, values, 0)


def transported_columns(power) -> PolyMatrix:
    """Six commutator columns, with source moved and coefficient fixed."""
    base = symbolic_commutator_columns(PLUS_WORDS)
    source = tuple(column[:3] for column in base)
    coefficient = tuple(column[3:] for column in base)
    columns = []
    for pair_index, pair in enumerate(PAIRS):
        wedge_column = wedge_image_poly(power, pair)
        moved_source = tuple(
            poly_add_many(
                poly_mul(wedge_column[old_pair], source[old_pair][central])
                for old_pair in range(6)
            )
            for central in range(3)
        )
        columns.append((*moved_source, *coefficient[pair_index]))
    return tuple(columns)


def rows_of_columns(columns: PolyMatrix) -> PolyMatrix:
    return tuple(tuple(columns[column][row] for column in range(6)) for row in range(6))


def determinant(matrix: PolyMatrix) -> int:
    size = len(matrix)
    # Signs disappear in characteristic two.
    return poly_add_many(
        reduce(
            poly_mul,
            (matrix[row][permutation[row]] for row in range(size)),
            ONE,
        )
        for permutation in permutations(range(size))
    )


def maximal_minor_gcd(matrix: PolyMatrix, rank: int) -> int:
    divisor = 0
    for selected_rows in combinations(range(len(matrix)), rank):
        for selected_columns in combinations(range(len(matrix[0])), rank):
            minor = tuple(
                tuple(matrix[row][column] for column in selected_columns)
                for row in selected_rows
            )
            value = determinant(minor)
            divisor = poly_gcd(divisor, value)
            if divisor == ONE:
                return ONE
    return divisor


def minor_witness(matrix: PolyMatrix, rank: int, value: int):
    for selected_rows in combinations(range(len(matrix)), rank):
        for selected_columns in combinations(range(len(matrix[0])), rank):
            minor = tuple(
                tuple(matrix[row][column] for column in selected_columns)
                for row in selected_rows
            )
            if determinant(minor) == value:
                return selected_rows, selected_columns
    return None


def degree(poly: int) -> int:
    return poly.bit_length() - 1


def audit(depth: int = 32) -> None:
    # Transport the source generators by T^{-n}; the kernel of their
    # commutator map is therefore wedge^2(T^n)K_0=K_n.
    transfer = block_inverse_transporter()
    power = identity_poly()
    divisors = []
    for n in range(depth):
        matrix = rows_of_columns(transported_columns(power))
        rank = fraction_rank(list(matrix))
        assert rank == (3 if n == 0 else 4)
        determinantal_divisors = tuple(
            maximal_minor_gcd(matrix, size) for size in range(1, rank + 1)
        )
        divisor = determinantal_divisors[-1]
        divisors.append(divisor)
        if n == 0:
            assert determinantal_divisors == (ONE, ONE, ONE)
        else:
            c_n = power[1][0]
            d_n = power[1][1]
            assert degree(c_n) == 2 * n - 1
            assert determinantal_divisors == (ONE, ONE, ONE, c_n)
            assert minor_witness(matrix, 4, poly_mul(c_n, c_n)) == (
                (0, 1, 3, 4), (1, 2, 3, 4)
            )
            assert minor_witness(matrix, 4, poly_mul(c_n, d_n)) == (
                (0, 2, 3, 4), (1, 2, 3, 4)
            )
        if n < 12:
            print(
                f"n={n} symbolic_rank={rank} "
                f"determinantal_divisor_degrees="
                f"{tuple(degree(value) for value in determinantal_divisors)} "
                f"last_divisor=0b{divisor:b}"
            )
        power = matrix_mul(power, transfer)

    assert divisors[0] == ONE
    print("one-sided symbolic commutator rank is 3 at level 0 and 4 thereafter")
    print("the rank jump is exactly the loss of the moving line from K_0 intersect K_n")
    print("Smith invariants at n>0 are 1,1,1,c_n with deg(c_n)=2n-1")


if __name__ == "__main__":
    audit()
