#!/usr/bin/env python3
"""Finite partition certificate for the terminal area-eight digon cases."""

from itertools import product

TARGETS = (
    (2, 2, 2, 2, 5, 11),
    (2, 2, 2, 3, 4, 11),
    (1, 2, 2, 2, 6, 11),
    (1, 2, 2, 4, 4, 11),
    (2, 2, 2, 2, 3, 13),
    (1, 2, 2, 2, 4, 13),
    (1, 2, 2, 2, 2, 15),
)

CORE_PARTITIONS = {
    2: {
        (1, 1, 5, 5), (1, 1, 2, 8), (1, 1, 1, 9),
        (1, 2, 3, 6), (2, 2, 4, 4), (3, 3, 3, 3),
    },
    3: {(1, 1, 4), (2, 2, 2)},
}


def contraction_matches(face_partition):
    digons = face_partition.count(2)
    remaining = list(face_partition)
    for _ in range(digons):
        remaining.remove(2)

    if digons == 4:
        # Four disjoint digon gadgets exhaust all vertices.  Connectedness
        # leaves one vertexless circle; each global face gains two corners
        # from every restored gadget.
        return [("circle", (8, 8))] if tuple(sorted(remaining)) == (8, 8) else []

    matches = []
    for incidences in product(range(digons + 1), repeat=len(remaining)):
        if sum(incidences) != 2 * digons:
            continue
        contracted = tuple(sorted(
            length - 2 * count
            for length, count in zip(remaining, incidences)
        ))
        if min(contracted) > 0 and contracted in CORE_PARTITIONS[digons]:
            matches.append((incidences, contracted))
    return matches


for target in TARGETS:
    matches = contraction_matches(target)
    print(target, "MATCHES", matches)
    assert not matches

print("PASS: no length-11/13/15 area-eight partition contracts to a planar cubic core")
