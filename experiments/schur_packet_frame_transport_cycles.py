#!/usr/bin/env python3
"""Enumerate the eight central-character transports of the paired frame.

This is a finite exact audit over F_2.  Besides the mandatory 101 -> 011
escape, it prints the full permutation and cycle decomposition induced by
every symbolic edge-group isomorphism.  The purpose is to decide whether an
oriented infinite construction needs a genuinely new level label or whether
one of the finite transports is already transient (it cannot be, but the
cycle lengths and return times constrain the smallest prefix construction).
"""
from __future__ import annotations

from itertools import product

from schur_packet_paired_commutant_frame import (
    CHARACTERS,
    COEFFICIENT_MINUS,
    COEFFICIENT_PLUS,
    FORBIDDEN,
    IDENTITY4,
    MINUS_WORDS,
    PLUS_WORDS,
    evaluated_frame_form,
    pull_form,
    rank_f2,
    relation_kernel,
    symbolic_commutator_columns,
    transformed_kernel,
)


def cycles(permutation: tuple[int, ...]) -> tuple[tuple[int, ...], ...]:
    unseen = set(range(len(permutation)))
    out = []
    while unseen:
        start = min(unseen)
        cycle = []
        point = start
        while point in unseen:
            unseen.remove(point)
            cycle.append(point)
            point = permutation[point]
        assert point == start
        out.append(tuple(cycle))
    return tuple(out)


def bits(index: int) -> str:
    return "".join(str(bit) for bit in CHARACTERS[index])


def audit() -> None:
    plus_forms = tuple(
        evaluated_frame_form(character, COEFFICIENT_PLUS, PLUS_WORDS)
        for character in CHARACTERS
    )
    minus_forms = tuple(
        evaluated_frame_form(character, COEFFICIENT_MINUS, MINUS_WORDS)
        for character in CHARACTERS
    )
    kernel = relation_kernel(symbolic_commutator_columns(PLUS_WORDS))
    assert kernel == relation_kernel(symbolic_commutator_columns(MINUS_WORDS))

    pattern_matrices: dict[tuple[int, ...], list[tuple[tuple[int, ...], ...]]] = {}
    for flat in product((0, 1), repeat=16):
        matrix = tuple(tuple(flat[4 * row : 4 * row + 4]) for row in range(4))
        if rank_f2(matrix) != 4 or transformed_kernel(matrix, kernel) != kernel:
            continue
        permutation = []
        for source_form in plus_forms:
            targets = tuple(
                index
                for index, target_form in enumerate(minus_forms)
                if source_form == pull_form(matrix, target_form)
            )
            assert len(targets) == 1
            permutation.append(targets[0])
        pattern_matrices.setdefault(tuple(permutation), []).append(matrix)

    forbidden_index = CHARACTERS.index(FORBIDDEN)
    reverse_index = CHARACTERS.index((0, 1, 1))
    assert len(pattern_matrices) == 8
    assert sum(len(matrices) for matrices in pattern_matrices.values()) == 32
    assert all(pattern[forbidden_index] == reverse_index for pattern in pattern_matrices)

    for number, (pattern, matrices) in enumerate(sorted(pattern_matrices.items()), 1):
        rendered = " ".join(f"{bits(i)}->{bits(target)}" for i, target in enumerate(pattern))
        rendered_cycles = " ".join(
            "(" + " ".join(bits(index) for index in cycle) + ")"
            for cycle in cycles(pattern)
        )
        return_time = next(
            step
            for step in range(1, 9)
            if __import__("functools").reduce(
                lambda point, _: pattern[point], range(step), forbidden_index
            )
            == forbidden_index
        )
        print(f"pattern {number}: multiplicity={len(matrices)} return(101)={return_time}")
        print("  ", rendered)
        print("  cycles", rendered_cycles)


if __name__ == "__main__":
    audit()
