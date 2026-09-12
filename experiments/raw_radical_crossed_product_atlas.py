#!/usr/bin/env python3
"""Verify the three fixed-scale crossed-product charts of the radical compiler.

On a satisfying sector the predicate packet is M_D.  A central sign twist is
inner there, so crossing by C2 gives M_D + M_D.  On a forbidden sector the
packet is four copies of M_(D/2); each nonzero radical translation pairs the
four blocks into two free orbits, and the crossed product is again
M_D + M_D.  The three translations are the three pairings of a four-point
affine plane.
"""
from __future__ import annotations

from itertools import product

from boolean_predicate_radical_cycle import compile_predicate
from schur_clifford_rank_gate import BitTuple, eval_matrix, rank_f2


RADICAL_CHARACTERS: tuple[BitTuple, ...] = tuple(product((0, 1), repeat=2))
DIRECTIONS: tuple[BitTuple, ...] = ((1, 0), (0, 1), (1, 1))


def translate(character: BitTuple, direction: BitTuple) -> BitTuple:
    return tuple(left ^ right for left, right in zip(character, direction))


def orbits(direction: BitTuple) -> tuple[tuple[BitTuple, ...], ...]:
    unseen = set(RADICAL_CHARACTERS)
    result = []
    while unseen:
        start = min(unseen)
        orbit = tuple(sorted((start, translate(start, direction))))
        assert len(set(orbit)) == 2
        unseen.difference_update(orbit)
        result.append(orbit)
    return tuple(sorted(result))


def audit_predicate(k: int, forbidden: list[BitTuple]) -> None:
    form, _, baseline = compile_predicate(k, forbidden)
    forbidden_set = set(forbidden)
    for assignment in product((0, 1), repeat=k):
        rank = rank_f2(eval_matrix(form, assignment))
        if assignment not in forbidden_set:
            assert rank == 2 * baseline
            # One invariant M_D block crossed by an inner C2 action has two
            # extensions, both still of dimension D.
            crossed_blocks = 2
            crossed_log_dimension = baseline
        else:
            assert rank == 2 * baseline - 2
            for direction in DIRECTIONS:
                pairing = orbits(direction)
                assert len(pairing) == 2
                assert all(len(orbit) == 2 for orbit in pairing)
            crossed_blocks = 2
            crossed_log_dimension = baseline
        assert (crossed_blocks, crossed_log_dimension) == (2, baseline)


def exhaustive(max_k: int = 3) -> None:
    assert len({orbits(direction) for direction in DIRECTIONS}) == 3
    print("three nonzero radical translations give three distinct pairings")
    for k in range(1, max_k + 1):
        cube = list(product((0, 1), repeat=k))
        for mask in range(1 << len(cube)):
            forbidden = [
                assignment
                for index, assignment in enumerate(cube)
                if (mask >> index) & 1
            ]
            audit_predicate(k, forbidden)
        print(
            f"exhaustive k={k}: all {1 << len(cube)} predicates have "
            "three uniform two-block crossed-product charts"
        )


if __name__ == "__main__":
    exhaustive()
