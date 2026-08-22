#!/usr/bin/env python3
"""Exact CFSG-order arithmetic from HS to O8+(2)."""

import json
import math


A8_ORDER = 20160
HS_ORDER = 44352000
O8P2_ORDER = 174182400


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
    rank_one = [
        (f"L2({q})", psl2_order(q))
        for q in prime_powers(703)
        if HS_ORDER < psl2_order(q) < O8P2_ORDER
    ]
    other = [
        ("J3", 50232960),
        ("U3(11)", 11**3 * (11**3 + 1) * (11**2 - 1) // math.gcd(3, 12)),
        ("S4(7)", 7**4 * (7**4 - 1) * (7**2 - 1) // 2),
        ("O8+(2)", O8P2_ORDER),
    ]
    rows = sorted(rank_one + other, key=lambda row: row[1])
    divisible = [name for name, order in rows if order % A8_ORDER == 0]
    if divisible != ["L2(449)", "S4(7)", "O8+(2)"]:
        raise AssertionError(f"A8-divisible interval list changed: {divisible}")
    if O8P2_ORDER // A8_ORDER != 8640:
        raise AssertionError("O8+(2)/A8 index calibration changed")
    if other[2][1] // A8_ORDER != 6860:
        raise AssertionError("S4(7)/A8 index calibration changed")

    print(json.dumps({
        "lower_endpoint": {"group": "HS", "order": HS_ORDER, "index": 2200},
        "upper_endpoint": {
            "group": "O8+(2)", "order": O8P2_ORDER, "index": 8640,
        },
        "simple_groups_strictly_after_HS_through_O8+(2)": [
            {
                "group": name,
                "order": order,
                "gcd_with_A8_order": math.gcd(order, A8_ORDER),
                "divisible_by_A8_order": order % A8_ORDER == 0,
            }
            for name, order in rows
        ],
        "A8_divisible_orders": divisible,
        "L2(449)_excluded_by": "2-rank(L2(q))<=2<4<=2-rank(A8)",
        "S4(7)_excluded_by": (
            "minimal faithful projective A8 degree in characteristic 7 is 8, not 4"
        ),
        "first_remaining_A8_overgroup": "O8+(2)",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
