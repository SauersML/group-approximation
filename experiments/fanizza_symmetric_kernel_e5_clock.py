#!/usr/bin/env python3
"""Verify the E5 clock for the Fanizza frame's symmetric rank-three kernel.

The rank-three frames found by ``fanizza_partial_center_frame_search.py`` all
have relation kernel

    K = span(e01, e23, e03 + e12).

The old transporter ``diag(S,S)`` fixes the third line.  This audit instead
uses the two-root E5 word ``diag(S,1,I2)``.  It fixes the first two relations
and moves the last as ``S^n J``, with one unique top-degree coordinate.  The
same calculation produces a rank-one relative hard pulse and a one-coordinate
Smith obstruction when the source frame moves and the coefficient frame is
held fixed.
"""
from __future__ import annotations

from functools import reduce

from e5_heisenberg_rank_one_boundary_pulse import (
    conjugate,
    elementary,
    identity,
    multiply,
    product,
)
from paired_frame_dual_character_clock import pullback_covector
from paired_frame_kernel_polynomial_stabilizer import (
    ONE,
    X,
    identity_poly,
    matrix_mul,
    poly_mul,
    wedge_image_poly,
)
from paired_frame_moving_kernel_orbit import (
    degree_profile,
    fraction_rank,
    move_relation,
)
from paired_frame_one_sided_rank_clock import (
    maximal_minor_gcd,
    rows_of_columns,
)
from schur_packet_paired_commutant_frame import PAIRS

PolyMatrix = tuple[tuple[int, ...], ...]


def one_sided_transporter() -> PolyMatrix:
    square = poly_mul(X, X)
    return (
        (ONE ^ square, X, 0, 0),
        (X, ONE, 0, 0),
        (0, 0, ONE, 0),
        (0, 0, 0, ONE),
    )


def one_sided_inverse() -> PolyMatrix:
    square = poly_mul(X, X)
    return (
        (ONE, X, 0, 0),
        (X, ONE ^ square, 0, 0),
        (0, 0, ONE, 0),
        (0, 0, 0, ONE),
    )


def symmetric_kernel_basis() -> tuple[tuple[int, ...], ...]:
    return (
        (1, 0, 0, 0, 0, 0),
        (0, 0, 0, 0, 0, 1),
        (0, 0, 1, 1, 0, 0),
    )


def symmetric_columns() -> tuple[tuple[int, ...], ...]:
    """A split map wedge^2(F2^4) -> F2^3 with the symmetric kernel."""
    return (
        (0, 0, 0),
        (1, 0, 0),
        (0, 1, 0),
        (0, 1, 0),
        (0, 0, 1),
        (0, 0, 0),
    )


def poly_add_many(values) -> int:
    return reduce(int.__xor__, values, 0)


def transported_combined_columns(power: PolyMatrix):
    base = symmetric_columns()
    columns = []
    for pair_index, pair in enumerate(PAIRS):
        wedge_column = wedge_image_poly(power, pair)
        moved_source = tuple(
            poly_add_many(
                poly_mul(wedge_column[old_pair], base[old_pair][central])
                for old_pair in range(6)
            )
            for central in range(3)
        )
        columns.append((*moved_source, *base[pair_index]))
    return tuple(columns)


def degree(polynomial: int) -> int:
    return polynomial.bit_length() - 1


def audit(depth: int = 48) -> None:
    size = 5
    # e01(x)e10(x)=diag(S,1,I2), so only the p-column is transported.
    transporter5 = product(
        elementary(size, 0, 1, X),
        elementary(size, 1, 0, X),
    )
    inverse5 = product(
        elementary(size, 1, 0, X),
        elementary(size, 0, 1, X),
    )
    assert multiply(transporter5, inverse5) == identity(size)
    assert multiply(inverse5, transporter5) == identity(size)
    p = (elementary(size, 0, 2, ONE), elementary(size, 1, 2, ONE))
    q = (elementary(size, 2, 3, ONE), elementary(size, 2, 4, ONE))
    for coordinate, root in enumerate(p):
        moved = conjugate(transporter5, inverse5, root)
        for target in range(2):
            assert moved[target][2] == one_sided_transporter()[target][coordinate]
    for root in q:
        assert conjugate(transporter5, inverse5, root) == root

    transfer = one_sided_transporter()
    inverse_transfer = one_sided_inverse()
    assert matrix_mul(transfer, inverse_transfer) == identity_poly()
    assert matrix_mul(inverse_transfer, transfer) == identity_poly()

    fixed_left, fixed_right, moving_zero = symmetric_kernel_basis()
    power = identity_poly()
    orbit = []
    smith_degrees = []
    stationary_hard = (0, ONE, 0, 0, ONE, 0)  # cross matrix I_2
    for n in range(depth):
        moved = tuple(
            move_relation(power, relation)
            for relation in (fixed_left, fixed_right, moving_zero)
        )
        assert moved[0] == fixed_left
        assert moved[1] == fixed_right
        assert fraction_rank(list(moved)) == 3
        if n == 0:
            assert moved[2] == moving_zero
        else:
            assert max(degree_profile(moved[2])) == 2 * n
            assert tuple((entry >> (2 * n)) & 1 for entry in moved[2]) == (
                0,
                0,
                1,
                0,
                0,
                0,
            )
        orbit.append(moved)

        # Move only the source copy.  At level zero the source and coefficient
        # hard forms cancel; every positive level has one top Pauli coordinate.
        pulse = tuple(
            transported ^ stationary
            for transported, stationary in zip(
                pullback_covector(power, stationary_hard), stationary_hard
            )
        )
        if n == 0:
            assert pulse == (0,) * 6
        else:
            assert max(degree_profile(pulse)) == 2 * n
            top_form = tuple((entry >> (2 * n)) & 1 for entry in pulse)
            assert top_form == (0, 1, 0, 0, 0, 0)

        combined = rows_of_columns(transported_combined_columns(power))
        combined_rank = fraction_rank(list(combined))
        assert combined_rank == (3 if n == 0 else 4)
        invariants = tuple(
            maximal_minor_gcd(combined, rank)
            for rank in range(1, combined_rank + 1)
        )
        if n == 0:
            assert invariants == (ONE, ONE, ONE)
        else:
            assert invariants == (ONE, ONE, ONE, power[1][0])
            assert degree(power[1][0]) == 2 * n - 1
        smith_degrees.append(tuple(degree(value) for value in invariants))
        if n < 8:
            print(
                f"n={n} moving_degrees={degree_profile(moved[2])} "
                f"pulse_degrees={degree_profile(pulse)} "
                f"Smith_degrees={smith_degrees[-1]}"
            )
        power = matrix_mul(power, transfer)

    for left in range(depth):
        for right in range(left + 1, depth):
            assert fraction_rank([*orbit[left], *orbit[right]]) == 4
    print("symmetric kernel orbit: fixed e01,e23 plus one moving cross line")
    print("two-root E5 word gives a unique degree-2n rank-one boundary pulse")
    print(f"positive-level Smith degree profiles begin {smith_degrees[1:8]}")


if __name__ == "__main__":
    audit()
