#!/usr/bin/env python3
"""Audit polynomial one-parameter shears preserving the paired-frame kernel.

The paired edge group is the quotient of wedge^2(F_2^4) by a fixed
three-dimensional relation kernel.  A binary transvection I+E_ab in its
stabilizer lifts to I+xE_ab over F_2[x] exactly when its exterior action
preserves the scalar extension of that kernel.  Opposite lifted
transvections would provide the strict polynomial-degree clock needed by the
one-sided reservoir attack.  The exhaustive result is negative: only one
square-zero parabolic survives.
"""
from __future__ import annotations

from functools import reduce
from itertools import product

from schur_packet_paired_commutant_frame import (
    PAIRS,
    PLUS_WORDS,
    relation_kernel,
    symbolic_commutator_columns,
)

PolyMatrix4 = tuple[
    tuple[int, int, int, int],
    tuple[int, int, int, int],
    tuple[int, int, int, int],
    tuple[int, int, int, int],
]

ONE = 1
X = 2


def poly_mul(left: int, right: int) -> int:
    out = 0
    while right:
        low = right & -right
        out ^= left << (low.bit_length() - 1)
        right ^= low
    return out


def matrix_mul(left: PolyMatrix4, right: PolyMatrix4) -> PolyMatrix4:
    return tuple(
        tuple(
            reduce(
                int.__xor__,
                (poly_mul(left[row][middle], right[middle][column]) for middle in range(4)),
                0,
            )
            for column in range(4)
        )
        for row in range(4)
    )  # type: ignore[return-value]


def identity_poly() -> PolyMatrix4:
    return tuple(tuple(ONE if row == column else 0 for column in range(4)) for row in range(4))  # type: ignore[return-value]


def transvection(row: int, column: int) -> PolyMatrix4:
    matrix = [list(line) for line in identity_poly()]
    matrix[row][column] = X
    return tuple(tuple(line) for line in matrix)  # type: ignore[return-value]


def wedge_image_poly(matrix: PolyMatrix4, pair: tuple[int, int]) -> tuple[int, ...]:
    first, second = pair
    return tuple(
        poly_mul(matrix[first][left], matrix[second][right])
        ^ poly_mul(matrix[first][right], matrix[second][left])
        for left, right in PAIRS
    )


def add_poly_vectors(*vectors: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        reduce(int.__xor__, (vector[index] for vector in vectors), 0)
        for index in range(6)
    )


def coefficient_vector(vector: tuple[int, ...], degree: int) -> tuple[int, ...]:
    return tuple((entry >> degree) & 1 for entry in vector)


def in_scalar_extended_kernel(vector: tuple[int, ...], kernel: set[tuple[int, ...]]) -> bool:
    top = max((entry.bit_length() for entry in vector), default=0)
    return all(coefficient_vector(vector, degree) in kernel for degree in range(top))


def preserves_kernel(matrix: PolyMatrix4, kernel: set[tuple[int, ...]]) -> bool:
    for relation in kernel:
        image = add_poly_vectors(
            *((wedge_image_poly(matrix, PAIRS[index])) for index, bit in enumerate(relation) if bit)
        )
        if not in_scalar_extended_kernel(image, kernel):
            return False
    return True


def degree(poly: int) -> int:
    return poly.bit_length() - 1


def audit(depth: int = 64) -> None:
    kernel = relation_kernel(symbolic_commutator_columns(PLUS_WORDS))
    assert len(kernel) == 8
    lifts = []
    for row, column in product(range(4), repeat=2):
        if row == column:
            continue
        shear = transvection(row, column)
        if preserves_kernel(shear, kernel):
            lifts.append((row, column))

    opposite_pairs = sorted(
        {(min(a, b), max(a, b)) for a, b in lifts if (b, a) in lifts}
    )
    print("polynomial transvection lifts:", lifts)
    print("opposite lifted pairs:", opposite_pairs)

    growing = []
    for first, second in product(lifts, repeat=2):
        transfer = matrix_mul(transvection(*first), transvection(*second))
        if not preserves_kernel(transfer, kernel):
            raise AssertionError((first, second, "product lost kernel"))
        power = identity_poly()
        maxima = []
        for _ in range(depth):
            power = matrix_mul(power, transfer)
            maxima.append(max(degree(entry) for row in power for entry in row))
        if all(right > left for left, right in zip(maxima, maxima[1:])):
            growing.append((first, second, tuple(maxima[:8])))

    print("strictly degree-growing ordered pairs:", len(growing))
    for record in growing:
        print(" ", record)
    assert lifts == [(0, 1), (0, 3), (2, 1), (2, 3)]
    assert opposite_pairs == []
    assert growing == []
    print("fixed-kernel polynomial degree clock: impossible")


if __name__ == "__main__":
    audit()
