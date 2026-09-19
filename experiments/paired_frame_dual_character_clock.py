#!/usr/bin/env python3
"""Exact dual-orbit audit for the paired-frame moving-kernel clock.

The relation kernel moves by K_n = wedge^2(T^n) K_0.  A central character
which is merely conjugated along with that kernel moves contragrediently:

    h_n = h_0 o wedge^2(T^{-n}).

This script determines the exact polynomial support of h_n and of its
successive increments.  It also separates the tautological transported
pairing h_n(K_n)=0 from the useful curvature h_0(L_n)=c_n^2.
"""
from __future__ import annotations

from functools import reduce

from paired_frame_kernel_polynomial_stabilizer import (
    ONE,
    PolyMatrix4,
    identity_poly,
    matrix_mul,
    poly_mul,
    wedge_image_poly,
)
from paired_frame_moving_kernel_orbit import (
    block_inverse_transporter,
    block_transporter,
    degree_profile,
    kernel_basis,
    move_relation,
)


Covector = tuple[int, int, int, int, int, int]


def pairing(covector: Covector, vector: tuple[int, ...]) -> int:
    return reduce(
        int.__xor__,
        (poly_mul(left, right) for left, right in zip(covector, vector)),
        0,
    )


def pullback_covector(matrix: PolyMatrix4, covector: Covector) -> Covector:
    """Return covector o wedge^2(matrix), in the standard wedge basis."""
    return tuple(
        pairing(covector, wedge_image_poly(matrix, pair))
        for pair in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
    )  # type: ignore[return-value]


def audit(depth: int = 64) -> None:
    transfer = block_transporter()
    inverse = block_inverse_transporter()
    assert matrix_mul(transfer, inverse) == identity_poly()
    assert matrix_mul(inverse, transfer) == identity_poly()

    basis = kernel_basis()
    hard: Covector = (0, ONE, 0, 0, 0, 0)
    forward_power = identity_poly()
    inverse_power = identity_poly()
    previous = hard

    for n in range(depth):
        moved = tuple(move_relation(forward_power, relation) for relation in basis)
        dual = pullback_covector(inverse_power, hard)

        # Conjugating both the kernel and its character is rank-neutral.
        assert all(pairing(dual, relation) == 0 for relation in moved)

        moving_line = moved[1]
        fixed_curvature = pairing(hard, moving_line)
        if n == 0:
            assert fixed_curvature == 0
            assert dual == hard
        else:
            # If S^n=[[a_n,c_n],[c_n,d_n]], then
            # h_n=(0,d_n^2,c_nd_n,c_nd_n,c_n^2,0).
            assert degree_profile(dual) == (-1, 4 * n - 4, 4 * n - 3, 4 * n - 3, 4 * n - 2, -1)
            assert fixed_curvature.bit_length() - 1 == 4 * n - 2

            increment = tuple(left ^ right for left, right in zip(dual, previous))
            assert max(degree_profile(increment)) == 4 * n - 2
            # The new top coefficient occurs only in e_13^*.
            top = 4 * n - 2
            top_coefficients = tuple((entry >> top) & 1 for entry in increment)
            assert top_coefficients == (0, 0, 0, 0, 1, 0)

        if n < 10:
            increment = tuple(left ^ right for left, right in zip(dual, previous))
            print(
                f"n={n} dual_degrees={degree_profile(dual)} "
                f"increment_degrees={degree_profile(increment)} "
                f"fixed_curvature_degree={fixed_curvature.bit_length() - 1}"
            )

        previous = dual
        forward_power = matrix_mul(forward_power, transfer)
        inverse_power = matrix_mul(inverse_power, inverse)

    print("transported character annihilates transported kernel at every level")
    print("successive dual increment has a unique new e_13^* coefficient in degree 4n-2")
    print("fixed hard character detects the moving line in the same degree 4n-2")


if __name__ == "__main__":
    audit()
