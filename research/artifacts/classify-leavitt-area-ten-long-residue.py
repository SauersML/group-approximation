#!/usr/bin/env python3
"""Arithmetic and forced-digon classification of the area-ten long residue.

The calculation uses no coefficient-word guesses.  Identities outside the
short group Q have length at least ten.  We enumerate the resulting face
budgets, contract every forced internal digon, and compare with the complete
small cubic ribbon-core face partitions.
"""

from collections import Counter
from itertools import combinations_with_replacement, permutations, product


def cycles(permutation):
    seen = set()
    result = []
    for start in range(len(permutation)):
        if start in seen:
            continue
        cycle = []
        current = start
        while current not in seen:
            seen.add(current)
            cycle.append(current)
            current = permutation[current]
        result.append(tuple(cycle))
    return tuple(result)


def connected(alpha, vertices):
    adjacency = [set() for _ in range(vertices)]
    for dart, twin in enumerate(alpha):
        adjacency[dart // 3].add(twin // 3)
    reached = {0}
    stack = [0]
    while stack:
        vertex = stack.pop()
        for other in adjacency[vertex] - reached:
            reached.add(other)
            stack.append(other)
    return len(reached) == vertices


def six_vertex_partitions():
    """All connected planar cubic six-vertex ribbon face partitions."""
    orientations = (1, 1, 1, -1, -1, -1)
    signs = sum(([1, 1, -1] if value == 1 else [1, -1, -1]
                 for value in orientations), [])
    positive = tuple(i for i, value in enumerate(signs) if value == 1)
    negative = tuple(i for i, value in enumerate(signs) if value == -1)
    rotation = tuple(3 * (i // 3) + (i % 3 + 1) % 3 for i in range(18))
    partitions = set()
    ribbons = 0
    for targets in permutations(negative):
        alpha = [None] * 18
        for left, right in zip(positive, targets):
            alpha[left], alpha[right] = right, left
        if not connected(alpha, 6):
            continue
        fs = cycles(tuple(rotation[alpha[i]] for i in range(18)))
        if len(fs) != 5:
            continue
        ribbons += 1
        partitions.add(tuple(sorted(map(len, fs))))
    return ribbons, partitions


CORE_PARTITIONS = {
    3: {
        (1, 1, 5, 5), (1, 1, 2, 8), (1, 1, 1, 9),
        (1, 2, 3, 6), (2, 2, 4, 4), (3, 3, 3, 3),
    },
    4: {(1, 1, 4), (2, 2, 2)},
}


def incidence_contractions(nondigons, digons, core_partitions):
    matches = set()
    for incidences in product(range(digons + 1), repeat=len(nondigons)):
        if sum(incidences) != 2 * digons:
            continue
        contracted = tuple(sorted(
            length - 2 * count
            for length, count in zip(nondigons, incidences)
        ))
        if min(contracted) > 0 and contracted in core_partitions:
            matches.add((incidences, contracted))
    return matches


def configurations():
    result = []
    for internal in combinations_with_replacement(range(2, 30), 6):
        # Q-nontrivial identities start at ten; every shorter identity is an
        # even Q-word.  Hence odd internal lengths 3,5,7,9 are forbidden.
        if any(length % 2 and length < 11 for length in internal):
            continue
        if not any(length >= 10 for length in internal):
            continue
        outer = 30 - sum(internal)
        if outer >= 1:
            result.append((internal, outer))
    return result


ribbons6, partitions6 = six_vertex_partitions()
assert partitions6
print("SIX_VERTEX_PLANAR_RIBBONS", ribbons6)
print("SIX_VERTEX_FACE_PARTITIONS", sorted(partitions6))

configs = configurations()
assert len(configs) == 52
print("CONFIGURATIONS", len(configs))
print("INTERNAL_DIGON_COUNTS", Counter(x[0].count(2) for x in configs))

survivors = []
for internal, outer in configs:
    digons = internal.count(2)
    nondigons = list(internal)
    for _ in range(digons):
        nondigons.remove(2)
    nondigons.append(outer)

    if digons == 5:
        matches = {("circle", (10, 10))} if tuple(sorted(nondigons)) == (10, 10) else set()
    elif digons == 4:
        matches = incidence_contractions(nondigons, digons, CORE_PARTITIONS[4])
    elif digons == 3:
        matches = incidence_contractions(nondigons, digons, CORE_PARTITIONS[3])
    elif digons == 2:
        matches = incidence_contractions(nondigons, digons, partitions6)
    else:
        # The two one-internal-digon budgets are handled by restoring one edge
        # in an eight-vertex core.  Record every arithmetically possible core
        # partition; even cores can be compared with the complete bipartite
        # atlas, while the odd list is the exact non-bipartite residue.
        matches = set()
        for incidences in product(range(3), repeat=len(nondigons)):
            if sum(incidences) != 2:
                continue
            contracted = tuple(sorted(
                length - 2 * count
                for length, count in zip(nondigons, incidences)
            ))
            if min(contracted) > 0:
                matches.add((incidences, contracted))

    if matches:
        survivors.append((internal, outer, digons, matches))
        print("SURVIVOR", internal, "OUTER", outer, "DIGONS", digons,
              "MATCHES", sorted(matches, key=str))

print("SURVIVOR_CONFIGURATIONS", len(survivors))
