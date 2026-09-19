#!/usr/bin/env python3
"""Construct an additive character which detects every triangular E5 pulse.

The symmetric Fanizza/E5 clock has an e02 pulse polynomial p_n with a fresh
leading monomial x^(2n).  Fresh leading degree gives a triangular *system*,
not a first-hit character.  Recursively choose the dual coefficient at 2n so
ell(p_n)=1 for every n.  The resulting character responds at all levels.
"""
from __future__ import annotations

from fanizza_symmetric_kernel_e5_clock import (
    identity_poly,
    matrix_mul,
    one_sided_transporter,
)
from paired_frame_dual_character_clock import pullback_covector
from paired_frame_moving_kernel_orbit import degree_profile

STATIONARY_HARD = (0, 1, 0, 0, 1, 0)


def evaluate(functional: int, polynomial: int) -> int:
    return (functional & polynomial).bit_count() & 1


def audit(depth: int = 64) -> None:
    transfer = one_sided_transporter()
    power = identity_poly()
    functional = 0
    pulses = []

    for level in range(1, depth + 1):
        power = matrix_mul(power, transfer)
        pulse = tuple(
            transported ^ stationary
            for transported, stationary in zip(
                pullback_covector(power, STATIONARY_HARD),
                STATIONARY_HARD,
            )
        )
        assert max(degree_profile(pulse)) == 2 * level
        top_form = tuple((entry >> (2 * level)) & 1 for entry in pulse)
        assert top_form == (0, 1, 0, 0, 0, 0)
        polynomial = pulse[1]
        assert polynomial.bit_length() - 1 == 2 * level

        # The coefficient of the new leading monomial is one and no earlier
        # pulse used it.  Choose its dual bit to make this pulse evaluate to 1.
        lower_value = evaluate(functional, polynomial)
        if lower_value == 0:
            functional ^= 1 << (2 * level)
        assert evaluate(functional, polynomial) == 1
        pulses.append(polynomial)

    assert all(evaluate(functional, polynomial) == 1 for polynomial in pulses)
    support = tuple(index for index in range(functional.bit_length()) if (functional >> index) & 1)
    first_detection = min(support)
    assert first_detection <= 2

    # For a finite-depth countermodel take any m above all occurring degrees
    # and read the same bits as a functional on F2[x]/(x^m-1).  No reduction
    # wraps, so all first `depth` pulse values remain one.  The quotient and
    # the orbit of this character under the polynomial transporter are finite.
    modulus_degree = 2 * depth + 1
    assert all(polynomial.bit_length() - 1 < modulus_degree for polynomial in pulses)

    print(f"depth={depth}")
    print(f"functional support={support}")
    print(
        "first pulse supports="
        + repr(
            tuple(
                tuple(index for index in range(polynomial.bit_length()) if (polynomial >> index) & 1)
                for polynomial in pulses[:16]
            )
        )
    )
    print(f"first detection degree={first_detection}")
    print(f"all {depth} pulse evaluations=1")
    print(f"finite quotient modulus may have degree {modulus_degree}")


if __name__ == "__main__":
    audit()
