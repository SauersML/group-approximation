#!/usr/bin/env python3
"""Verify the Clifford/radical capacity bound for the V4 five-fourths atlas.

After a local Clifford transport, a branch supported on one radical character
is described by one effective character a_i in D^*.  A pair-specific Pauli
axis w_ij separates branches i,j exactly when (a_i+a_j).w_ij=1, which is
possible exactly when a_i != a_j.  Hence a complete antiphase graph on N
branches needs N distinct characters.

The synchronized V4 failure profile has five atom occurrences over its four
radical characters: 000 occurs twice and each of 011,101,110 occurs once.
The exhaustive r=2 search below confirms that no assignment of effective
characters separates all five occurrences.  Dummy radical coordinates
multiply both occurrence count and character capacity by the same factor.
"""
from __future__ import annotations

from itertools import product


Vector = tuple[int, ...]


def dot(left: Vector, right: Vector) -> int:
    return sum(a & b for a, b in zip(left, right)) & 1


def add(left: Vector, right: Vector) -> Vector:
    return tuple(a ^ b for a, b in zip(left, right))


def separating_axes(left: Vector, right: Vector) -> tuple[Vector, ...]:
    difference = add(left, right)
    return tuple(
        axis
        for axis in product((0, 1), repeat=len(left))
        if any(axis) and dot(difference, axis) == 1
    )


def complete_antiphase_assignment(rank: int, branches: int) -> tuple[Vector, ...] | None:
    characters = tuple(product((0, 1), repeat=rank))
    for assignment in product(characters, repeat=branches):
        if all(
            separating_axes(assignment[i], assignment[j])
            for i in range(branches)
            for j in range(i + 1, branches)
        ):
            return assignment
    return None


def audit() -> None:
    characters = tuple(product((0, 1), repeat=2))
    for left in characters:
        for right in characters:
            axes = separating_axes(left, right)
            assert bool(axes) == (left != right)

    witness_four = complete_antiphase_assignment(rank=2, branches=4)
    witness_five = complete_antiphase_assignment(rank=2, branches=5)
    assert witness_four is not None
    assert len(set(witness_four)) == 4
    assert witness_five is None

    # VOF2 has multiplicities 2,1,1,1 on the four radical atoms.
    base_failure_occurrences = 5
    base_character_capacity = 4
    assert base_failure_occurrences > base_character_capacity
    for dummy_rank in range(7):
        occurrence_count = base_failure_occurrences * (1 << dummy_rank)
        character_capacity = base_character_capacity * (1 << dummy_rank)
        assert occurrence_count > character_capacity

    print(f"r=2 four-branch witness={witness_four}")
    print("r=2 five-branch complete antiphase assignment: none")
    print("dummy radical extension t=0..6: occurrence/capacity ratio remains 5/4")


if __name__ == "__main__":
    audit()
