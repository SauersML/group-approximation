#!/usr/bin/env python3
"""Exhaustive checks for the seven-point one-ghost Fano relation.

The mathematical proofs live in Cairn.  This script independently replays the
finite claims used by the Fano-cap compiler:

* the cap count by size is 1, 7, 21, 28, 7;
* the seven maximal caps are the nonzero character one-fibres;
* the minimum blocking sets are exactly the seven Fano lines; and
* in arities one through three, the only Boolean polymorphisms of ``R_*`` are
  the coordinate projections.

It uses only the Python standard library and exits nonzero if any certificate
changes.
"""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations, product


Bit = int
Vector = tuple[Bit, ...]


def xor(left: Vector, right: Vector) -> Vector:
    return tuple(a ^ b for a, b in zip(left, right, strict=True))


FANO_POINTS: tuple[Vector, ...] = tuple(
    point for point in product((0, 1), repeat=3) if any(point)
)
RSTAR: tuple[Vector, ...] = tuple(
    word
    for word in product((0, 1), repeat=4)
    if sum(word) % 2 == 1 and word != (1, 0, 0, 0)
)
FANO_LINES = frozenset(
    frozenset((left, right, xor(left, right)))
    for left, right in combinations(FANO_POINTS, 2)
)


def subsets(items: tuple[Vector, ...]):
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def is_cap(candidate: tuple[Vector, ...]) -> bool:
    points = frozenset(candidate)
    return all(not line <= points for line in FANO_LINES)


def dot(left: Vector, right: Vector) -> Bit:
    return sum(a * b for a, b in zip(left, right, strict=True)) % 2


def truth_table_value(table: int, inputs: Vector) -> Bit:
    index = sum(bit << position for position, bit in enumerate(inputs))
    return (table >> index) & 1


def is_rstar_polymorphism(arity: int, table: int) -> bool:
    for inputs in product(RSTAR, repeat=arity):
        output = tuple(
            truth_table_value(table, tuple(word[coordinate] for word in inputs))
            for coordinate in range(4)
        )
        if output not in RSTAR:
            return False
    return True


def projection_table(arity: int, coordinate: int) -> int:
    table = 0
    for inputs in product((0, 1), repeat=arity):
        index = sum(bit << position for position, bit in enumerate(inputs))
        table |= inputs[coordinate] << index
    return table


def main() -> None:
    assert len(FANO_LINES) == 7

    caps = tuple(candidate for candidate in subsets(FANO_POINTS) if is_cap(candidate))
    cap_counts = Counter(map(len, caps))
    assert cap_counts == Counter({0: 1, 1: 7, 2: 21, 3: 28, 4: 7})

    character_caps = {
        functional: frozenset(point for point in FANO_POINTS if dot(functional, point))
        for functional in FANO_POINTS
    }
    maximal_caps = {frozenset(cap) for cap in caps if len(cap) == 4}
    assert set(character_caps.values()) == maximal_caps
    assert all(any(frozenset(cap) <= maximal for maximal in maximal_caps) for cap in caps)

    blocking_sets = tuple(
        frozenset(candidate)
        for candidate in subsets(FANO_POINTS)
        if all(frozenset(candidate) & line for line in FANO_LINES)
    )
    minimum_blocking_size = min(map(len, blocking_sets))
    minimum_blocking_sets = {blocker for blocker in blocking_sets if len(blocker) == 3}
    assert minimum_blocking_size == 3
    assert minimum_blocking_sets == set(FANO_LINES)

    polymorphisms: dict[int, list[int]] = {}
    for arity in range(1, 4):
        tables = [
            table
            for table in range(1 << (1 << arity))
            if is_rstar_polymorphism(arity, table)
        ]
        projections = [projection_table(arity, coordinate) for coordinate in range(arity)]
        assert tables == projections
        polymorphisms[arity] = tables

    cap_table = {
        "".join(map(str, functional)): [
            "".join(map(str, word))
            for word in RSTAR
            if dot(functional, word[1:]) == 1
        ]
        for functional in FANO_POINTS
    }
    print(
        json.dumps(
            {
                "cap_counts": dict(sorted(cap_counts.items())),
                "maximal_caps": cap_table,
                "minimum_blocking_sets": len(minimum_blocking_sets),
                "polymorphism_counts": {
                    arity: len(tables) for arity, tables in polymorphisms.items()
                },
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
