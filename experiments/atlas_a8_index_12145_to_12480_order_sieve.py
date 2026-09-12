#!/usr/bin/env python3
"""Exact simple-order arithmetic from M24 to G2(4)."""

import json
import math


A8_ORDER = 20160
M24_ORDER = 244823040
G24_ORDER = 251596800


def main():
    rows = [("G2(4)", G24_ORDER)]
    if [name for name, _order in rows] != ["G2(4)"]:
        raise AssertionError("post-M24 simple-order interval changed")
    divisible = [name for name, order in rows if order % A8_ORDER == 0]
    if divisible != ["G2(4)"]:
        raise AssertionError(f"A8-divisible interval list changed: {divisible}")
    if G24_ORDER // A8_ORDER != 12480:
        raise AssertionError("G2(4)/A8 index calibration changed")

    print(json.dumps({
        "lower_endpoint": {"group": "M24", "order": M24_ORDER, "index": 12144},
        "upper_endpoint": {"group": "G2(4)", "order": G24_ORDER, "index": 12480},
        "simple_groups_strictly_after_M24_through_G2(4)": [
            {
                "group": name,
                "order": order,
                "gcd_with_A8_order": math.gcd(order, A8_ORDER),
                "divisible_by_A8_order": order % A8_ORDER == 0,
            }
            for name, order in rows
        ],
        "A8_divisible_orders": divisible,
        "first_arithmetic_A8_overgroup_candidate": "G2(4)",
        "G2(4)_A8_index_if_contained": G24_ORDER // A8_ORDER,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
