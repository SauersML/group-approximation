#!/usr/bin/env python3
"""Verify that shifted dyadic E_5 pulses detect every positive valuation.

For each r>=2, choose the largest dyadic n with 4n-2<=r and shift the p
half of the frame by x^(r-(4n-2)).  The resulting pulse has unique top term
x^r e_13^*.  A character first detected in degree r therefore sees exactly
one alternating pair.
"""
from __future__ import annotations

from functools import cache

from paired_frame_dual_character_clock import pullback_covector
from paired_frame_kernel_polynomial_stabilizer import identity_poly, matrix_mul
from paired_frame_moving_kernel_orbit import block_inverse_transporter, degree_profile
from schur_packet_paired_commutant_frame import rank_f2


HARD_FORM = (0, 1, 1, 1, 0, 0)


def shift(vector: tuple[int, ...], amount: int) -> tuple[int, ...]:
    return tuple(entry << amount for entry in vector)


def coefficient(vector: tuple[int, ...], degree: int) -> tuple[int, ...]:
    return tuple((entry >> degree) & 1 for entry in vector)


def alternating_matrix(wedge: tuple[int, ...]) -> list[list[int]]:
    matrix = [[0 for _ in range(4)] for _ in range(4)]
    for value, (left, right) in zip(
        wedge, ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
    ):
        matrix[left][right] = matrix[right][left] = value
    return matrix


def dyadic_power(n: int):
    assert n > 0 and n & (n - 1) == 0
    transfer = block_inverse_transporter()
    power = identity_poly()
    for _ in range(n):
        power = matrix_mul(power, transfer)
    return power


def pulse_at(n: int) -> tuple[int, ...]:
    power = dyadic_power(n)
    return tuple(
        transported ^ stationary
        for transported, stationary in zip(
            pullback_covector(power, HARD_FORM), HARD_FORM
        )
    )


def chosen_dyadic(valuation: int) -> int:
    assert valuation >= 2
    n = 1
    while 8 * n - 2 <= valuation:
        n *= 2
    assert 4 * n - 2 <= valuation < 8 * n - 2
    return n


@cache
def root_word_cost(exponent: int) -> int:
    """Balanced Steinberg-commutator upper bound for e_ij(x^exponent)."""
    if exponent <= 1:
        return 1
    left = exponent // 2
    right = exponent - left
    return 2 * root_word_cost(left) + 2 * root_word_cost(right)


def audit(max_valuation: int = 1024) -> None:
    pulse_cache = {}
    for valuation in range(2, max_valuation + 1):
        n = chosen_dyadic(valuation)
        pulse = pulse_cache.setdefault(n, pulse_at(n))
        displacement = valuation - (4 * n - 2)
        shifted = shift(pulse, displacement)
        assert max(degree_profile(shifted)) == valuation
        evaluated = coefficient(shifted, valuation)
        assert evaluated == (0, 0, 0, 0, 1, 0)
        assert rank_f2(alternating_matrix(evaluated)) == 2
        if displacement:
            assert root_word_cost(displacement) <= 4 * displacement * displacement

    print(f"all valuations 2..{max_valuation} compile to the single e_13 Pauli pair")
    print("the coefficient shift has a balanced Steinberg word of quadratic length")


if __name__ == "__main__":
    audit()
