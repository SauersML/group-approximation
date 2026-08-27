#!/usr/bin/env python3
"""Compile a Boolean predicate into a fixed-word radical rank drop.

For every forbidden assignment a, make a cyclic affine block C_a=I+N_a.
The cycle edge labels are the literals [x_i=a_i].  Its determinant is
1+product_i[x_i=a_i], so it is invertible off a and has the constant all-one
left and right kernel at a.  Direct-summing the blocks and symmetrizing gives
an alternating affine form of rank 2N-2f(x).  On a forbidden sector, fixed
products of the row and column generators are the two raw radical words.
"""
from __future__ import annotations

from itertools import product
from typing import Callable

from schur_clifford_rank_gate import (
    Affine,
    BitTuple,
    affine_add,
    affine_one,
    affine_zero,
    eval_matrix,
    literal,
    rank_f2,
)


def assignment_cycle(k: int, assignment: BitTuple) -> list[list[Affine]]:
    if len(assignment) != k:
        raise ValueError("assignment has wrong arity")
    size = max(1, k)
    block = [[affine_zero(k) for _ in range(size)] for _ in range(size)]
    for index in range(size):
        block[index][index] = affine_one(k)
    if k == 0:
        block[0][0] = affine_add(block[0][0], affine_one(0))
        return block
    for index, bit in enumerate(assignment):
        target = (index + 1) % k
        block[index][target] = affine_add(
            block[index][target], literal(k, index, bit)
        )
    return block


def block_diagonal(blocks: list[list[list[Affine]]], k: int) -> list[list[Affine]]:
    size = sum(len(block) for block in blocks)
    matrix = [[affine_zero(k) for _ in range(size)] for _ in range(size)]
    offset = 0
    for block in blocks:
        for row in range(len(block)):
            for column in range(len(block)):
                matrix[offset + row][offset + column] = block[row][column]
        offset += len(block)
    return matrix


def symmetrize(matrix: list[list[Affine]], k: int) -> list[list[Affine]]:
    size = len(matrix)
    form = [[affine_zero(k) for _ in range(2 * size)] for _ in range(2 * size)]
    for row in range(size):
        for column in range(size):
            form[row][size + column] = matrix[row][column]
            form[size + column][row] = matrix[row][column]
    return form


def compile_predicate(
    k: int, forbidden: list[BitTuple]
) -> tuple[list[list[Affine]], dict[BitTuple, tuple[int, int]], int]:
    blocks = [assignment_cycle(k, assignment) for assignment in forbidden]
    matrix = block_diagonal(blocks, k)
    block_size = max(1, k)
    raw_radicals = {
        assignment: (index * block_size, (index + 1) * block_size)
        for index, assignment in enumerate(forbidden)
    }
    return symmetrize(matrix, k), raw_radicals, len(matrix)


def matrix_vector(matrix: list[list[int]], vector: list[int]) -> list[int]:
    return [
        sum(entry * value for entry, value in zip(row, vector)) & 1
        for row in matrix
    ]


def verify_predicate(k: int, predicate: Callable[..., bool]) -> tuple[int, int]:
    cube = list(product((0, 1), repeat=k))
    forbidden = [assignment for assignment in cube if predicate(*assignment)]
    form, radical_blocks, baseline = compile_predicate(k, forbidden)
    for assignment in cube:
        evaluated = eval_matrix(form, assignment)
        expected = 2 * baseline - 2 * int(predicate(*assignment))
        assert rank_f2(evaluated) == expected
        if assignment in radical_blocks:
            start, stop = radical_blocks[assignment]
            row_word = [0] * (2 * baseline)
            column_word = [0] * (2 * baseline)
            for index in range(start, stop):
                row_word[index] = 1
                column_word[baseline + index] = 1
            assert matrix_vector(evaluated, row_word) == [0] * (2 * baseline)
            assert matrix_vector(evaluated, column_word) == [0] * (2 * baseline)
    return len(form), baseline


def exhaustive(max_k: int = 3) -> None:
    for k in range(1, max_k + 1):
        cube = list(product((0, 1), repeat=k))
        for mask in range(1 << len(cube)):
            verify_predicate(
                k,
                lambda *assignment, mask=mask: bool(
                    (mask >> cube.index(tuple(assignment))) & 1
                ),
            )
        print(f"exhaustive k={k}: verified all {1 << len(cube)} predicates")


def and_demo() -> None:
    size, baseline = verify_predicate(2, lambda x, y: x == y == 1)
    print("AND violation block C=[[1,x],[y,1]]")
    print(f"symmetrized size={size}, generic rank={2 * baseline}, hot rank={2 * baseline - 2}")
    print("hot raw radical words are p_0 p_1 and q_0 q_1")


if __name__ == "__main__":
    and_demo()
    exhaustive()
