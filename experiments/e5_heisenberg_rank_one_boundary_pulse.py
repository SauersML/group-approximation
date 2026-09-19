#!/usr/bin/env python3
"""Verify the E_5(F_2[x]) realization of the one-sided boundary pulse.

The (2,1,2) upper-block Heisenberg subgroup has two commuting p roots, two
commuting q roots, and four independent cross commutator roots.  A four-root
elementary word acts on both p and q coordinates by the degree-growing
matrix S.  On the relative hard character, its nth inverse conjugate has one
unique leading wedge coefficient, producing a rank-one Pauli pulse on the
corresponding first-detection character layer.
"""
from __future__ import annotations

from functools import reduce

from paired_frame_dual_character_clock import pullback_covector
from paired_frame_kernel_polynomial_stabilizer import ONE, X, poly_mul
from paired_frame_moving_kernel_orbit import (
    block_inverse_transporter,
    degree_profile,
)


Matrix = tuple[tuple[int, ...], ...]


def identity(size: int) -> Matrix:
    return tuple(tuple(ONE if row == column else 0 for column in range(size)) for row in range(size))


def multiply(left: Matrix, right: Matrix) -> Matrix:
    size = len(left)
    return tuple(
        tuple(
            reduce(
                int.__xor__,
                (poly_mul(left[row][middle], right[middle][column]) for middle in range(size)),
                0,
            )
            for column in range(size)
        )
        for row in range(size)
    )


def elementary(size: int, row: int, column: int, coefficient: int) -> Matrix:
    out = [list(line) for line in identity(size)]
    out[row][column] = coefficient
    return tuple(tuple(line) for line in out)


def product(*matrices: Matrix) -> Matrix:
    return reduce(multiply, matrices, identity(len(matrices[0])))


def conjugate(conjugator: Matrix, inverse: Matrix, element: Matrix) -> Matrix:
    return product(conjugator, element, inverse)


def commutator(left: Matrix, right: Matrix) -> Matrix:
    # Every root generator used below is an involution.
    return product(left, right, left, right)


def audit(depth: int = 64) -> None:
    size = 5
    p = (elementary(size, 0, 2, ONE), elementary(size, 1, 2, ONE))
    q = (elementary(size, 2, 3, ONE), elementary(size, 2, 4, ONE))
    center = tuple(
        tuple(elementary(size, i, j, ONE) for j in (3, 4))
        for i in (0, 1)
    )
    assert commutator(p[0], p[1]) == identity(size)
    assert commutator(q[0], q[1]) == identity(size)
    for i in range(2):
        for j in range(2):
            assert commutator(p[i], q[j]) == center[i][j]

    # D=diag(S,1,S^-1), S=(I+xE_01)(I+xE_10).
    upper = product(
        elementary(size, 0, 1, X),
        elementary(size, 4, 3, X),
    )
    lower = product(
        elementary(size, 1, 0, X),
        elementary(size, 3, 4, X),
    )
    transporter = product(upper, lower)
    transporter_inverse = product(lower, upper)
    assert multiply(transporter, transporter_inverse) == identity(size)
    assert multiply(transporter_inverse, transporter) == identity(size)

    inverse_block = block_inverse_transporter()
    for coordinate, root in enumerate(p):
        moved = conjugate(transporter_inverse, transporter, root)
        for target in range(2):
            assert moved[target][2] == inverse_block[target][coordinate]
    for coordinate, root in enumerate(q):
        moved = conjugate(transporter_inverse, transporter, root)
        for target in range(2):
            assert moved[2][3 + target] == inverse_block[2 + coordinate][2 + target]

    # The stationary minus hard sector has source and coefficient form H, so
    # they cancel at level zero.  Only the source form is conjugated.
    hard_form = (0, ONE, ONE, ONE, 0, 0)
    power = (
        inverse_block[0], inverse_block[1], inverse_block[2], inverse_block[3]
    )
    for n in range(1, depth + 1):
        pulse = tuple(
            transported ^ stationary
            for transported, stationary in zip(
                pullback_covector(power, hard_form), hard_form
            )
        )
        top = 4 * n - 2
        assert max(degree_profile(pulse)) == top
        assert tuple((entry >> top) & 1 for entry in pulse) == (0, 0, 0, 0, 1, 0)
        if n & (n - 1) == 0:
            level = n.bit_length() - 1
            c_n = power[1][0]
            d_n = power[0][0]
            assert c_n == 1 << (2 * n - 1)
            expected_d = ONE
            for j in range(1, level + 1):
                expected_d ^= 1 << (2 * n - (1 << j))
            assert d_n == expected_d
            support = {
                degree
                for entry in pulse
                for degree in range(entry.bit_length())
                if (entry >> degree) & 1
            }
            assert min(support) == 2 * n - 1
            assert max(support) == 4 * n - 2
            assert all(2 * n - 1 <= degree <= 4 * n - 2 for degree in support)
        if n < depth:
            power = multiply(power, inverse_block)

    print("p-p and q-q commute; the four p-q commutators are independent E_5 roots")
    print("a four-root elementary word acts by diag(S,1,S^-1)")
    print("the nth relative hard pulse has unique top coefficient e_13^* x^(4n-2)")
    print("at n=2^k its whole support is in the disjoint band [2n-1,4n-2]")


if __name__ == "__main__":
    audit()
