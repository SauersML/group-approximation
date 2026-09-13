#!/usr/bin/env python3
"""Bounded exact replay for the finite-density-moment artifact; run on MSI."""

from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import prod


def matchings(vertices):
    if not vertices:
        yield ()
        return
    first, *rest = vertices
    for index, partner in enumerate(rest):
        remaining = tuple(rest[:index] + rest[index + 1 :])
        for tail in matchings(remaining):
            yield ((first, partner),) + tail


def components(size, sampled):
    parent = list(range(size))

    def root(vertex):
        while parent[vertex] != vertex:
            vertex = parent[vertex]
        return vertex

    for matching in sampled:
        for left, right in matching:
            parent[root(left)] = root(right)
    return tuple(root(vertex) for vertex in range(size))


def even_near_equal(colors, alphabet):
    counts = Counter(colors)
    sizes = [counts[color] for color in range(alphabet)]
    return all(size % 2 == 0 for size in sizes) and max(sizes) - min(sizes) <= 2


def replay():
    cases = 0
    tuples_checked = 0
    for n in (1, 2, 3):
        all_matchings = tuple(matchings(tuple(range(2 * n))))
        count = len(all_matchings)
        laws = (
            tuple(Fraction(1, count) for _ in all_matchings),
            tuple(Fraction(index + 1, count * (count + 1) // 2)
                  for index in range(count)),
            tuple(Fraction(index == 0) for index in range(count)),
        )
        for weights in laws:
            support = tuple((matching, weight) for matching, weight
                            in zip(all_matchings, weights) if weight)
            for alphabet in (2, 3):
                colorings = tuple(product(range(alphabet), repeat=2 * n))
                densities = {
                    colors: alphabet ** n * sum(
                        (weight for matching, weight in support
                         if all(colors[left] == colors[right]
                                for left, right in matching)),
                        Fraction(0),
                    )
                    for colors in colorings
                }
                for restricted in (False, True):
                    def admissible(colors):
                        return not restricted or even_near_equal(colors, alphabet)

                    selected = tuple(colors for colors in colorings if admissible(colors))
                    theta = sum((densities[colors] for colors in selected), Fraction(0))
                    theta /= alphabet ** (2 * n)
                    for q in (2, 3):
                        direct = sum((densities[colors] ** q for colors in selected), Fraction(0))
                        direct /= alphabet ** (2 * n)
                        overlap = Fraction(0)
                        for sampled in product(support, repeat=q):
                            partitions = tuple(item[0] for item in sampled)
                            tuple_weight = prod(item[1] for item in sampled)
                            labels = components(2 * n, partitions)
                            roots = tuple(sorted(set(labels)))
                            assignments = 0
                            for values in product(range(alphabet), repeat=len(roots)):
                                lookup = dict(zip(roots, values))
                                colors = tuple(lookup[label] for label in labels)
                                assignments += admissible(colors)
                            overlap += tuple_weight * assignments
                            tuples_checked += 1
                        overlap *= alphabet ** ((q - 2) * n)
                        assert direct == overlap, (n, alphabet, restricted, q, direct, overlap)
                        support_mass_bound = Fraction(len(support), alphabet ** n)
                        assert theta ** q <= direct * support_mass_bound ** (q - 1)
                        cases += 1
    return {
        "status": "passed",
        "scope": "n=1,2,3; m=2,3; q=2,3; three rational laws; two coloring sets",
        "cases": cases,
        "matching_tuples_checked": tuples_checked,
        "identities": ["balanced union-component density moment", "Holder support inequality"],
        "proves_ugc": False,
    }


if __name__ == "__main__":
    print(json.dumps(replay(), sort_keys=True))
