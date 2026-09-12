#!/usr/bin/env python3
"""Exact canonical-path congestion certificate for the A4 packet alphabet.

For each element of A8=GL(4,2), choose the first shortest word found by BFS in
one fixed ordering of the ten packet letters.  If w_g has length ell(g), the
usual telescoping/Cauchy estimate weights every occurrence of a packet letter
s in w_g by ell(g).  Summing these weights gives a rigorous Poincare/commutant
constant for every amplification of the regular representation.

This is exact integer arithmetic.  No numerical linear algebra is used.
"""

import json
from collections import Counter, deque
from fractions import Fraction

from atlas_a4_packet_generation import packet_letters
from atlas_two_chart_search import I4, gf2_mul, matrix_key

# Indices refer to the packet letters after sorting by matrix_key.  This order
# was found by a finite routing search and is frozen as part of the certificate;
# replaying the script verifies the resulting congestion counts.
ROUTING_ORDER = [8, 1, 7, 9, 5, 0, 6, 2, 3, 4]
EXPECTED_MAX_WEIGHT = 113452
GROUP_ORDER = 20160


def shortest_word_routing():
    letters, _ = packet_letters()
    letters = sorted(letters, key=matrix_key)
    ordered = [letters[i] for i in ROUTING_ORDER]

    root = matrix_key(I4)
    distance = {root: 0}
    parent = {}
    parent_label = {}
    frontier = deque([I4.copy()])

    while frontier:
        x = frontier.popleft()
        x_key = matrix_key(x)
        for ordered_label, generator in enumerate(ordered):
            y = gf2_mul(x, generator)
            y_key = matrix_key(y)
            if y_key in distance:
                continue
            distance[y_key] = distance[x_key] + 1
            parent[y_key] = x_key
            parent_label[y_key] = ordered_label
            frontier.append(y)

    if len(distance) != GROUP_ORDER:
        raise AssertionError(f"routing reached {len(distance)} elements")

    path_counts = {root: (0,) * len(ordered)}
    weighted_ordered = [0] * len(ordered)
    ordinary_ordered = [0] * len(ordered)

    for vertex, depth in sorted(distance.items(), key=lambda item: item[1]):
        if vertex == root:
            continue
        counts = list(path_counts[parent[vertex]])
        counts[parent_label[vertex]] += 1
        path_counts[vertex] = tuple(counts)
        for label, count in enumerate(counts):
            ordinary_ordered[label] += count
            weighted_ordered[label] += depth * count

    weighted = [0] * len(ordered)
    ordinary = [0] * len(ordered)
    for ordered_label, sorted_label in enumerate(ROUTING_ORDER):
        weighted[sorted_label] = weighted_ordered[ordered_label]
        ordinary[sorted_label] = ordinary_ordered[ordered_label]

    max_weight = max(weighted)
    if max_weight != EXPECTED_MAX_WEIGHT:
        raise AssertionError(
            f"routing certificate changed: {max_weight} != {EXPECTED_MAX_WEIGHT}"
        )

    coefficient_sq = Fraction(max_weight, 2 * GROUP_ORDER)
    return {
        "group_order": GROUP_ORDER,
        "routing_order_on_sorted_packet_letters": ROUTING_ORDER,
        "distance_layers": dict(sorted(Counter(distance.values()).items())),
        "weighted_occurrence_counts": weighted,
        "ordinary_occurrence_counts": ordinary,
        "max_weighted_occurrence_count": max_weight,
        "commutant_coefficient_squared": {
            "numerator": coefficient_sq.numerator,
            "denominator": coefficient_sq.denominator,
        },
        "commutant_coefficient_decimal": float(coefficient_sq) ** 0.5,
    }


def main():
    print(json.dumps(shortest_word_routing(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
