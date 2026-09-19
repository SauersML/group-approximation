#!/usr/bin/env python3
"""Audit strict degree drift of two alternating F_2[x] shears.

Polynomials are bitsets: bit i is the coefficient of x^i.  The product

    T = [[1,x],[0,1]] [[1,0],[x,1]]
      = [[1+x^2,x],[x,1]]

is the smallest fixed word that avoids the order-two return of either shear.
For n>=1 the degrees of T^n are [[2n,2n-1],[2n-1,2n-2]].
"""
from __future__ import annotations

Matrix2 = tuple[tuple[int, int], tuple[int, int]]

ONE = 1
X = 2
IDENTITY: Matrix2 = ((ONE, 0), (0, ONE))
FORWARD: Matrix2 = ((ONE, X), (0, ONE))
OPPOSITE: Matrix2 = ((ONE, 0), (X, ONE))


def poly_mul(left: int, right: int) -> int:
    out = 0
    while right:
        low = right & -right
        out ^= left << (low.bit_length() - 1)
        right ^= low
    return out


def matrix_mul(left: Matrix2, right: Matrix2) -> Matrix2:
    return tuple(
        tuple(
            poly_mul(left[row][0], right[0][column])
            ^ poly_mul(left[row][1], right[1][column])
            for column in range(2)
        )
        for row in range(2)
    )  # type: ignore[return-value]


def degree(poly: int) -> int:
    return poly.bit_length() - 1


def degree_profile(matrix: Matrix2) -> tuple[tuple[int, int], tuple[int, int]]:
    return tuple(tuple(degree(entry) for entry in row) for row in matrix)  # type: ignore[return-value]


def audit(depth: int = 512) -> None:
    transfer = matrix_mul(FORWARD, OPPOSITE)
    assert transfer == ((ONE ^ (X << 1), X), (X, ONE))
    power = IDENTITY
    profiles = []
    for n in range(1, depth + 1):
        power = matrix_mul(power, transfer)
        profile = degree_profile(power)
        target = ((2 * n, 2 * n - 1), (2 * n - 1, 2 * n - 2))
        assert profile == target, (n, profile, target)
        assert all(entry >> degree(entry) == 1 for row in power for entry in row)
        if n <= 12:
            profiles.append((n, profile))
    assert len({profile[0][0] for _, profile in profiles}) == len(profiles)
    print("T=[[1+x^2,x],[x,1]] = forward * opposite")
    for n, profile in profiles:
        print(f"n={n:2d} degrees={profile}")
    print(f"verified strict leading-degree drift through n={depth}")


if __name__ == "__main__":
    audit()
