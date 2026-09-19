#!/usr/bin/env python3
"""Exact independent-conjugator search for the two-packet equation.

The candidate conjugators are the distinct genuinely mixed elements through
word length four in the eight elementary s/t root involutions.  The global
trace theorem reduces the full Cartesian square to pairs whose packet
supports have odd intersection; only those pairs are multiplied out.
"""

from functools import lru_cache
from pathlib import Path
import runpy
import sys


sys.argv = ["verify-kl-gate-c3-corner.py", "--final-only", "--family=none"]
data = runpy.run_path(
    str(Path(__file__).with_name("verify-kl-gate-c3-corner.py"))
)

base_delta = data["base_delta"]
corner_a = data["corner_a"]
corner_b = data["corner_b"]
gr_add = data["gr_add"]
gr_mul = data["gr_mul"]
mat = data["mat"]
mul = data["mul"]
ONE = data["ONE"]
packet = data["packet"]
S0 = data["S0"]
S1 = data["S1"]
T0 = data["T0"]
T1 = data["T1"]
theta2 = data["theta2"]
ZERO = data["ZERO"]

coefficients = (("s0", S0), ("s1", S1), ("t0", T0), ("t1", T1))
generators = []
for name, coefficient in coefficients:
    generators.append(("U" + name, theta2(mat(ONE, coefficient, ZERO, ONE))))
    generators.append(("L" + name, theta2(mat(ONE, ZERO, coefficient, ONE))))

generator_by_name = dict(generators)
seen = {ONE: ((), ONE)}
frontier = [((), ONE)]
snapshots = {}
for length in range(1, 5):
    next_frontier = []
    for word, unit in frontier:
        for name, generator in generators:
            if word and word[-1] == name:
                continue
            new_word = word + (name,)
            new_unit = mul(unit, generator)
            if new_unit not in seen:
                seen[new_unit] = (new_word, new_unit)
                next_frontier.append((new_word, new_unit))
    frontier = next_frontier
    if length in (3, 4):
        snapshots[length] = dict(seen)


def genuinely_mixed(snapshot):
    candidates = []
    for word, unit in snapshot.values():
        if unit == ONE:
            continue
        if not any("s" in token for token in word):
            continue
        if not any("t" in token for token in word):
            continue
        inverse = ONE
        for token in reversed(word):
            inverse = mul(inverse, generator_by_name[token])
        assert mul(unit, inverse) == mul(inverse, unit) == ONE
        candidates.append((word, unit, inverse))
    return candidates


@lru_cache(maxsize=400_000)
def cached_unit_product(left, right):
    return mul(left, right)


def group_ring_product(left, right):
    result = set()
    for left_unit in left:
        for right_unit in right:
            value = cached_unit_product(left_unit, right_unit)
            if value in result:
                result.remove(value)
            else:
                result.add(value)
    return result


def audit(length, expected_candidates, expected_survivors):
    candidates = genuinely_mixed(snapshots[length])
    assert len(candidates) == expected_candidates

    packets = [packet(unit, inverse) for _, unit, inverse in candidates]

    # These finite instances agree with the global linear-trace theorem.
    assert all(ONE not in gr_mul(corner_a, value) for value in packets)
    assert all(ONE not in gr_mul(value, corner_b) for value in packets)

    survivors = []
    for left_index, left_packet in enumerate(packets):
        for right_index, right_packet in enumerate(packets):
            if len(left_packet.intersection(right_packet)) % 2 == 1:
                survivors.append((left_index, right_index))

    assert len(survivors) == expected_survivors

    left_terms = [gr_mul(corner_a, value) for value in packets]
    right_terms = [gr_mul(value, corner_b) for value in packets]
    for left_index, right_index in survivors:
        product = group_ring_product(
            packets[left_index], packets[right_index]
        )
        residue = gr_add(
            base_delta,
            right_terms[left_index],
            left_terms[right_index],
            product,
        )
        assert residue

    print(
        f"length {length}: {len(candidates)} mixed conjugators, "
        f"{len(candidates) ** 2} ordered pairs, "
        f"{len(survivors)} odd-intersection survivors, no solutions"
    )


audit(3, expected_candidates=204, expected_survivors=208)
audit(4, expected_candidates=1254, expected_survivors=1394)
