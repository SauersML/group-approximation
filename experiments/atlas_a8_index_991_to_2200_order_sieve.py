#!/usr/bin/env python3
"""Exact order sieve from A11 to the Higman--Sims group."""

import json
import math


A8_ORDER = 20160
A11_ORDER = 19958400
HS_ORDER = 44352000


def is_prime(number):
    return number >= 2 and all(
        number % divisor for divisor in range(2, math.isqrt(number) + 1)
    )


def prime_powers(bound):
    values = set()
    for prime in range(2, bound + 1):
        if not is_prime(prime):
            continue
        value = prime
        while value <= bound:
            values.add(value)
            value *= prime
    return sorted(values)


def psl2_order(q):
    return q * (q * q - 1) // math.gcd(2, q - 1)


def main():
    # q=449 is already above HS.
    rank_one = [
        (f"L2({q})", psl2_order(q))
        for q in prime_powers(448)
        if A11_ORDER < psl2_order(q) < HS_ORDER
    ]
    expected = [
        343, 347, 349, 353, 359, 361, 367, 373, 379, 383,
        389, 397, 401, 409, 419, 421, 431, 433, 439, 443,
    ]
    if [int(name[3:-1]) for name, _order in rank_one] != expected:
        raise AssertionError("PSL2 interval parameters changed")

    other = [
        ("Sz(32)", 32**2 * (32**2 + 1) * (32 - 1)),
        ("L3(9)", 9**3 * (9**3 - 1) * (9**2 - 1) // math.gcd(3, 8)),
        ("U3(9)", 9**3 * (9**3 + 1) * (9**2 - 1) // math.gcd(3, 10)),
        ("HS", HS_ORDER),
    ]
    rows = sorted(rank_one + other, key=lambda row: row[1])
    divisible = [name for name, order in rows if order % A8_ORDER == 0]
    if divisible != ["L3(9)", "HS"]:
        raise AssertionError("A8-divisible order list changed")
    if HS_ORDER // A8_ORDER != 2200:
        raise AssertionError("HS index calibration changed")

    print(json.dumps({
        "lower_endpoint": {"group": "A11", "order": A11_ORDER, "index": 990},
        "upper_endpoint": {"group": "HS", "order": HS_ORDER, "index": 2200},
        "simple_groups_after_A11_through_HS": [
            {
                "group": name,
                "order": order,
                "gcd_with_A8_order": math.gcd(order, A8_ORDER),
                "divisible_by_A8_order": order % A8_ORDER == 0,
            }
            for name, order in rows
        ],
        "A8_divisible_orders": divisible,
        "L3(9)_excluded_by": "2-rank(PGL3(9))<=2<4=2-rank(A8)",
        "first_remaining_A8_overgroup": "HS",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
