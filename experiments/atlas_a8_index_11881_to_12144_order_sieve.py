#!/usr/bin/env python3
"""Exact simple-order arithmetic from A12 to M24."""

import json
import math


A8_ORDER = 20160
A12_ORDER = math.factorial(12) // 2
M24_ORDER = 244823040


def psl2_order(q):
    return q * (q * q - 1) // math.gcd(2, q - 1)


def main():
    rows = [
        ("L2(787)", psl2_order(787)),
        ("M24", M24_ORDER),
    ]
    if rows != [("L2(787)", 243721308), ("M24", 244823040)]:
        raise AssertionError("post-A12 simple-order interval changed")
    divisible = [name for name, order in rows if order % A8_ORDER == 0]
    if divisible != ["M24"]:
        raise AssertionError(f"A8-divisible interval list changed: {divisible}")
    if M24_ORDER // A8_ORDER != 12144:
        raise AssertionError("M24/A8 index calibration changed")

    print(json.dumps({
        "lower_endpoint": {"group": "A12", "order": A12_ORDER, "index": 11880},
        "upper_endpoint": {"group": "M24", "order": M24_ORDER, "index": 12144},
        "simple_groups_strictly_after_A12_through_M24": [
            {
                "group": name,
                "order": order,
                "gcd_with_A8_order": math.gcd(order, A8_ORDER),
                "divisible_by_A8_order": order % A8_ORDER == 0,
            }
            for name, order in rows
        ],
        "A8_divisible_orders": divisible,
        "first_remaining_A8_overgroup": "M24",
        "M24_A8_index": M24_ORDER // A8_ORDER,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
