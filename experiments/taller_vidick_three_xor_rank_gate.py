#!/usr/bin/env python3
"""Exhaust the minimal Clifford rank gate for every three-XOR equation."""
from __future__ import annotations

from itertools import product

from schur_clifford_rank_gate import rank_f2


def verify() -> None:
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
    print("three-XOR: both right-hand sides and all 16 sectors verified")


if __name__ == "__main__":
    verify()
