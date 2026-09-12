#!/usr/bin/env python3
"""Exhaust the minimal Clifford rank gate for every three-XOR equation."""
from __future__ import annotations

from itertools import product

from schur_clifford_rank_gate import rank_f2


Matrix = list[list[int]]


def multiply(left: Matrix, right: Matrix) -> Matrix:
    return [
        [
            sum(left[row][index] * right[index][column] for index in range(len(right)))
            for column in range(len(right[0]))
        ]
        for row in range(len(left))
    ]


def tensor(left: Matrix, right: Matrix) -> Matrix:
    return [
        [left_entry * right_entry for left_entry in left_row for right_entry in right_row]
        for left_row in left
        for right_row in right
    ]


def scale(value: int, matrix: Matrix) -> Matrix:
    return [[value * entry for entry in row] for row in matrix]


def verify() -> None:
    identity = [[1, 0], [0, 1]]
    pauli_x = [[0, 1], [1, 0]]
    pauli_z = [[1, 0], [0, -1]]
    p_1 = tensor(pauli_x, identity)
    q_1 = tensor(pauli_z, identity)
    p_2 = tensor(identity, pauli_x)
    for right_hand_side in (0, 1):
        for assignment in product((0, 1), repeat=3):
            violation = right_hand_side ^ assignment[0] ^ assignment[1] ^ assignment[2]
            matrix = [[1, 0], [0, violation]]
            assert rank_f2(matrix) == 1 + violation
            commutator_phase = (-1) ** violation
            selector_phase = (-1) ** (
                right_hand_side + sum(assignment)
            )
            assert commutator_phase == selector_phase
            q_2 = tensor(identity, pauli_z if violation else identity)
            identity_4 = tensor(identity, identity)
            for generator in (p_1, q_1, p_2, q_2):
                assert multiply(generator, generator) == identity_4
            assert multiply(p_1, q_1) == scale(-1, multiply(q_1, p_1))
            assert multiply(p_2, q_2) == scale(
                commutator_phase, multiply(q_2, p_2)
            )
            assert multiply(p_1, q_2) == multiply(q_2, p_1)
            assert multiply(p_2, q_1) == multiply(q_1, p_2)
    print("three-XOR: both right-hand sides and all 16 sectors verified")


if __name__ == "__main__":
    verify()
