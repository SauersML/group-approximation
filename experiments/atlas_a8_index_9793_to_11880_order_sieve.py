#!/usr/bin/env python3
"""Exact simple-order arithmetic from O8-(2) to A12."""

import json
import math


A8_ORDER = 20160
O8M2_ORDER = 197406720
A12_ORDER = math.factorial(12) // 2


def is_prime(number):
    return number >= 2 and all(
        number % divisor for divisor in range(2, int(number ** 0.5) + 1)
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
        for q in prime_powers(773)
        if O8M2_ORDER < psl2_order(q) < A12_ORDER
    ]
    other = [
        ("3D4(2)", 211341312),
        ("L3(11)", 212427600),
        ("A12", A12_ORDER),
    ]
    rows = sorted(rank_one + other, key=lambda row: row[1])
    expected_names = [
        "L2(739)", "L2(743)", "3D4(2)", "L2(751)", "L3(11)",
        "L2(757)", "L2(761)", "L2(769)", "L2(773)", "A12",
    ]
    if [name for name, _order in rows] != expected_names:
        raise AssertionError("post-O8-(2) simple-order interval changed")
    divisible = [name for name, order in rows if order % A8_ORDER == 0]
    if divisible != ["A12"]:
        raise AssertionError(f"A8-divisible interval list changed: {divisible}")
    if A12_ORDER // A8_ORDER != 11880:
        raise AssertionError("A12/A8 index calibration changed")

    print(json.dumps({
        "lower_endpoint": {"group": "O8-(2)", "order": O8M2_ORDER, "index": 9792},
        "upper_endpoint": {"group": "A12", "order": A12_ORDER, "index": 11880},
        "simple_groups_strictly_after_O8-(2)_through_A12": [
            {
                "group": name,
                "order": order,
                "gcd_with_A8_order": math.gcd(order, A8_ORDER),
                "divisible_by_A8_order": order % A8_ORDER == 0,
            }
            for name, order in rows
        ],
        "A8_divisible_orders": divisible,
        "first_remaining_A8_overgroup": "A12",
        "A12_A8_natural_orbit_decomposition": [8, 1, 1, 1, 1],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
