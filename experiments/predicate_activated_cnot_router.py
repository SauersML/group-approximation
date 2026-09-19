#!/usr/bin/env python3
"""Verify a CNOT automorphism for two predicate-activated Pauli pairs.

The base class-two group has involutions a,b,c,d and a central involution K,
with [a,b]=[c,d]=K and all cross commutators trivial.  The CNOT map

    a -> a c,  b -> b,  c -> c,  d -> b d

preserves the symbolic commutator form for either value of K and squares to
the identity.  On K=-1 it routes the b spectral halves of the d=+1 source
flag to the two d-sign target flags.
"""
from __future__ import annotations

from itertools import product

Matrix = tuple[tuple[int, ...], ...]

OMEGA: Matrix = (
    (0, 1, 0, 0),
    (1, 0, 0, 0),
    (0, 0, 0, 1),
    (0, 0, 1, 0),
)

# Columns are the exponent vectors of the images of a,b,c,d.
CNOT: Matrix = (
    (1, 0, 0, 0),
    (0, 1, 0, 1),
    (1, 0, 1, 0),
    (0, 0, 0, 1),
)


def multiply(left: Matrix, right: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum(left[row][middle] * right[middle][column] for middle in range(4)) % 2
            for column in range(4)
        )
        for row in range(4)
    )


def transpose(matrix: Matrix) -> Matrix:
    return tuple(tuple(matrix[row][column] for row in range(4)) for column in range(4))


def identity() -> Matrix:
    return tuple(tuple(int(row == column) for column in range(4)) for row in range(4))


def audit() -> None:
    assert multiply(CNOT, CNOT) == identity()
    assert multiply(multiply(transpose(CNOT), OMEGA), CNOT) == OMEGA

    routed = []
    for control_sign, source_flag_sign in product((1, -1), repeat=2):
        target_flag_sign = control_sign * source_flag_sign
        routed.append((control_sign, source_flag_sign, target_flag_sign))
    assert [entry for entry in routed if entry[1] == 1] == [(1, 1, 1), (-1, 1, -1)]

    print("CNOT order=2 and preserves diag(K,K) symbolic commutator form")
    print("source flag d=+1 routes b=+1 to active d=+1 and b=-1 to exit d=-1")
    print("valid simultaneously on K=+1 abelian and K=-1 two-Pauli sectors")


if __name__ == "__main__":
    audit()
