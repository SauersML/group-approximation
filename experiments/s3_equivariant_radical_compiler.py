#!/usr/bin/env python3
"""Verify the universal S3-equivariant raw-radical predicate compiler.

Starting with the literal-cycle matrix C, form the symmetric border

    S = [[0,C],[C^T,D]],

where D has one marked diagonal coordinate in every forbidden block.  S is
invertible off the forbidden atoms and has a fixed one-dimensional kernel on
the matching atom.  The alternating form H tensor S therefore loses exactly
one Pauli qubit, and its two-dimensional radical carries the natural
GL2(F2)=S3 action on the H factor.
"""
from __future__ import annotations

from itertools import product

from boolean_predicate_radical_cycle import assignment_cycle, block_diagonal
from schur_clifford_rank_gate import (
    Affine,
    BitTuple,
    affine_one,
    affine_zero,
    eval_matrix,
    rank_f2,
)


def symmetric_border(
    k: int, forbidden: list[BitTuple]
) -> tuple[list[list[Affine]], dict[BitTuple, tuple[int, int]], int]:
    blocks = [assignment_cycle(k, assignment) for assignment in forbidden]
    cycle = block_diagonal(blocks, k)
    size = len(cycle)
    symmetric = [[affine_zero(k) for _ in range(2 * size)] for _ in range(2 * size)]
    for row in range(size):
        for column in range(size):
            symmetric[row][size + column] = cycle[row][column]
            symmetric[size + column][row] = cycle[row][column]
    block_size = max(1, k)
    supports = {}
    for block_index, assignment in enumerate(forbidden):
        start = block_index * block_size
        stop = start + block_size
        symmetric[size + start][size + start] = affine_one(k)
        supports[assignment] = (start, stop)
    return symmetric, supports, size


def hyperbolic_tensor(symmetric: list[list[Affine]], k: int) -> list[list[Affine]]:
    size = len(symmetric)
    alternating = [[affine_zero(k) for _ in range(2 * size)] for _ in range(2 * size)]
    for row in range(size):
        for column in range(size):
            alternating[row][size + column] = symmetric[row][column]
            alternating[size + row][column] = symmetric[row][column]
    return alternating


def matrix_vector(matrix: list[list[int]], vector: list[int]) -> list[int]:
    return [sum(a * b for a, b in zip(row, vector)) & 1 for row in matrix]


def verify_predicate(k: int, forbidden: list[BitTuple]) -> None:
    symmetric, supports, cycle_size = symmetric_border(k, forbidden)
    alternating = hyperbolic_tensor(symmetric, k)
    symmetric_size = len(symmetric)
    forbidden_set = set(forbidden)
    for assignment in product((0, 1), repeat=k):
        evaluated_symmetric = eval_matrix(symmetric, assignment)
        evaluated_alternating = eval_matrix(alternating, assignment)
        assert all(
            evaluated_symmetric[row][column]
            == evaluated_symmetric[column][row]
            for row in range(len(evaluated_symmetric))
            for column in range(len(evaluated_symmetric))
        )
        assert all(
            evaluated_alternating[row][column]
            == evaluated_alternating[column][row]
            for row in range(len(evaluated_alternating))
            for column in range(len(evaluated_alternating))
        )
        assert all(
            evaluated_alternating[index][index] == 0
            for index in range(len(evaluated_alternating))
        )
        hot = assignment in forbidden_set
        assert rank_f2(evaluated_symmetric) == 2 * cycle_size - int(hot)
        assert rank_f2(evaluated_alternating) == 4 * cycle_size - 2 * int(hot)
        if hot:
            start, stop = supports[assignment]
            kernel = [0] * symmetric_size
            for index in range(start, stop):
                kernel[index] = 1
            assert matrix_vector(evaluated_symmetric, kernel) == [0] * symmetric_size
            first = kernel + [0] * symmetric_size
            second = [0] * symmetric_size + kernel
            assert matrix_vector(evaluated_alternating, first) == [0] * (2 * symmetric_size)
            assert matrix_vector(evaluated_alternating, second) == [0] * (2 * symmetric_size)


def exhaustive(max_k: int = 3) -> None:
    for k in range(1, max_k + 1):
        cube = list(product((0, 1), repeat=k))
        for mask in range(1 << len(cube)):
            forbidden = [
                assignment
                for index, assignment in enumerate(cube)
                if (mask >> index) & 1
            ]
            verify_predicate(k, forbidden)
        print(
            f"exhaustive k={k}: all {1 << len(cube)} predicates have "
            "one S3-natural raw radical qubit per violation"
        )


if __name__ == "__main__":
    exhaustive()
