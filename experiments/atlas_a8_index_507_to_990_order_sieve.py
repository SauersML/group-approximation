#!/usr/bin/env python3
"""Exact finite-simple order sieve from M23 to A11.

The accompanying Cairn proof supplies the CFSG family bounds reducing the
open interval to PSL(2,q), PSL(3,8), PSU(5,2), and the Tits group.  This script
performs the remaining prime-power and divisibility arithmetic exactly.
"""

import json
import math


A8_ORDER = 20160
M23_ORDER = 10200960
A11_ORDER = 19958400


def is_prime(number):
    if number < 2:
        return False
    return all(number % divisor for divisor in range(2, math.isqrt(number) + 1))


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
    # q=343 is already above A11, so q<=342 is exhaustive for PSL(2,q).
    rank_one = [
        (f"L2({q})", psl2_order(q))
        for q in prime_powers(342)
        if M23_ORDER < psl2_order(q) < A11_ORDER
    ]
    expected_rank_one_parameters = [
        256, 277, 281, 283, 289, 293, 307, 311, 313, 317, 331, 337
    ]
    if [int(name[3:-1]) for name, _order in rank_one] != expected_rank_one_parameters:
        raise AssertionError("PSL2 interval parameters changed")

    exceptional_rows = [
        ("U5(2)", 2**10 * (2**2 - 1) * (2**3 + 1) * (2**4 - 1) * (2**5 + 1)),
        ("L3(8)", 8**3 * (8**3 - 1) * (8**2 - 1) // math.gcd(3, 7)),
        ("2F4(2)'", 17971200),
    ]
    rows = sorted(rank_one + exceptional_rows + [("A11", A11_ORDER)], key=lambda row: row[1])
    if any(order % A8_ORDER == 0 for name, order in rows if name != "A11"):
        raise AssertionError("an interior simple order became divisible by |A8|")
    if A11_ORDER // A8_ORDER != 990:
        raise AssertionError("A11 index calibration changed")

    print(json.dumps({
        "lower_endpoint": {"group": "M23", "order": M23_ORDER, "index": 506},
        "upper_endpoint": {"group": "A11", "order": A11_ORDER, "index": 990},
        "interior_and_endpoint_simple_groups": [
            {
                "group": name,
                "order": order,
                "gcd_with_A8_order": math.gcd(order, A8_ORDER),
                "divisible_by_A8_order": order % A8_ORDER == 0,
            }
            for name, order in rows
        ],
        "only_A8_divisible_order_after_M23_through_A11": "A11",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
