#!/usr/bin/env python3
"""Exact simple-order interval from O8+(2) to O8-(2)."""

import json
import math


A8_ORDER = 20160
O8P2_ORDER = 174182400
O8M2_ORDER = 197406720


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
        for q in prime_powers(733)
        if O8P2_ORDER < psl2_order(q) < O8M2_ORDER
    ]
    rows = sorted(rank_one + [("O8-(2)", O8M2_ORDER)], key=lambda row: row[1])
    expected_names = ["L2(709)", "L2(719)", "L2(727)", "L2(729)",
                      "L2(733)", "O8-(2)"]
    if [name for name, _order in rows] != expected_names:
        raise AssertionError("simple-order interval list changed")
    divisible = [name for name, order in rows if order % A8_ORDER == 0]
    if divisible != ["O8-(2)"]:
        raise AssertionError(f"A8-divisible interval list changed: {divisible}")
    if O8M2_ORDER // A8_ORDER != 9792:
        raise AssertionError("O8-(2)/A8 index calibration changed")

    print(json.dumps({
        "lower_endpoint": {"group": "O8+(2)", "order": O8P2_ORDER, "index": 8640},
        "upper_endpoint": {"group": "O8-(2)", "order": O8M2_ORDER, "index": 9792},
        "simple_groups_strictly_after_O8+(2)_through_O8-(2)": [
            {
                "group": name,
                "order": order,
                "gcd_with_A8_order": math.gcd(order, A8_ORDER),
                "divisible_by_A8_order": order % A8_ORDER == 0,
            }
            for name, order in rows
        ],
        "A8_divisible_orders": divisible,
        "first_remaining_A8_overgroup": "O8-(2)",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
