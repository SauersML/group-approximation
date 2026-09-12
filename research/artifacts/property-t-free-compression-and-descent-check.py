#!/usr/bin/env python3
"""Exact finite checks for two Property-(T)-free proof fences.

The clock/shift calculations use monomial matrices represented by a target
index and an exponent of an n-th root of unity.  No numerical tolerance is
used there.  The final floating-point table calibrates the polar-compression
loss from PCD10.
"""

from __future__ import annotations

import cmath
import math


Monomial = tuple[tuple[int, int], ...]


def multiply(left: Monomial, right: Monomial, modulus: int) -> Monomial:
    return tuple(
        (left[target][0], (phase + left[target][1]) % modulus)
        for target, phase in right
    )


def inverse(matrix: Monomial, modulus: int) -> Monomial:
    result: list[tuple[int, int] | None] = [None] * len(matrix)
    for source, (target, phase) in enumerate(matrix):
        result[target] = (source, (-phase) % modulus)
    assert all(entry is not None for entry in result)
    return tuple(entry for entry in result if entry is not None)


def commutator(left: Monomial, right: Monomial, modulus: int) -> Monomial:
    return multiply(
        multiply(
            multiply(left, right, modulus), inverse(left, modulus), modulus
        ),
        inverse(right, modulus),
        modulus,
    )


def check_compression_model(n: int) -> None:
    assert n % 2 == 1
    m = (n + 1) // 2
    dimension = 2 * n
    identity: Monomial = tuple((j, 0) for j in range(dimension))
    clock: Monomial = tuple((j, j % n) for j in range(dimension))
    multiplier: Monomial = tuple(
        ((j // n) * n + ((j % n) * m) % n, 0) for j in range(dimension)
    )
    flip_shift: Monomial = tuple(
        ((1 - j // n) * n + ((j % n) + (1 if j // n else -1)) % n, 0)
        for j in range(dimension)
    )

    assert multiply(flip_shift, flip_shift, n) == identity
    assert multiply(
        multiply(multiplier, clock, n), inverse(multiplier, n), n
    ) == multiply(clock, clock, n)

    transported = multiply(
        multiply(multiplier, flip_shift, n), inverse(multiplier, n), n
    )
    expected = tuple((j, (-m if j < n else m) % n) for j in range(dimension))
    assert commutator(transported, clock, n) == expected


def polar_defect(theta: float) -> float:
    c, s = math.cos(theta), math.sin(theta)
    scalar = c * c - 1j * s * s
    phase = scalar / abs(scalar)
    return abs(1 - phase)


def main() -> None:
    dimensions = (3, 5, 7, 9, 11, 25)
    for n in dimensions:
        check_compression_model(n)
    print("exact monomial identities:", ", ".join(map(str, dimensions)))

    for theta in (0.1, 0.03, 0.01):
        defect = polar_defect(theta)
        print(
            f"theta={theta:g}  defect={defect:.12g}  "
            f"defect/theta^2={defect / theta**2:.9f}"
        )


if __name__ == "__main__":
    main()
