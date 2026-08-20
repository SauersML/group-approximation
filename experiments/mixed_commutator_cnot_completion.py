#!/usr/bin/env python3
"""Verify the minimal four-generator mixed-central CNOT packet.

The control pair has commutator K, the flag pair has commutator J, and two
cross commutators equal K and KJ.  This coupling makes

    a <-> c,  b -> b,  d -> b d

an involutive automorphism preserving both commutators and generator squares.
The script also exhausts the uncoupled block-diagonal four-generator packet
and confirms that it has no automorphism with b -> b and d -> b d.
"""
from __future__ import annotations

from itertools import product

Vector = tuple[int, ...]
Matrix = tuple[Vector, ...]
PAIRS = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
FORM_K: Vector = (1, 0, 1, 1, 0, 0)
FORM_J: Vector = (0, 0, 1, 0, 0, 1)
CNOT: Matrix = (
    (0, 0, 1, 0),
    (0, 1, 0, 0),
    (1, 0, 0, 0),
    (0, 1, 0, 1),
)


def basis(index: int) -> Vector:
    return tuple(int(position == index) for position in range(4))


def add(left: Vector, right: Vector) -> Vector:
    return tuple(a ^ b for a, b in zip(left, right))


def rank(vectors: list[Vector]) -> int:
    work = [list(vector) for vector in vectors]
    pivot = 0
    for column in range(4):
        row = next((row for row in range(pivot, len(work)) if work[row][column]), None)
        if row is None:
            continue
        work[pivot], work[row] = work[row], work[pivot]
        for other in range(len(work)):
            if other != pivot and work[other][column]:
                work[other] = [a ^ b for a, b in zip(work[other], work[pivot])]
        pivot += 1
    return pivot


def pairing(left: Vector, right: Vector, form: Vector) -> int:
    return sum(
        value * ((left[first] & right[second]) ^ (left[second] & right[first]))
        for value, (first, second) in zip(form, PAIRS)
    ) & 1


def square(vector: Vector, form: Vector) -> int:
    return sum(
        value * vector[first] * vector[second]
        for value, (first, second) in zip(form, PAIRS)
    ) & 1


def preserves(columns: Matrix, form: Vector) -> bool:
    return all(
        pairing(columns[first], columns[second], form)
        == pairing(basis(first), basis(second), form)
        for first in range(4)
        for second in range(4)
    ) and all(square(column, form) == 0 for column in columns)


def form_rank(form: Vector) -> int:
    matrix = [[0] * 4 for _ in range(4)]
    for value, (left, right) in zip(form, PAIRS):
        matrix[left][right] = matrix[right][left] = value
    return rank([tuple(row) for row in matrix])


def compose(left: Matrix, right: Matrix) -> Matrix:
    return tuple(
        tuple(
            sum(left[middle][row] * right[column][middle] for middle in range(4)) & 1
            for row in range(4)
        )
        for column in range(4)
    )


def audit() -> None:
    identity = tuple(basis(index) for index in range(4))
    assert rank(list(CNOT)) == 4
    assert compose(CNOT, CNOT) == identity
    assert CNOT[1] == basis(1)
    assert CNOT[3] == add(basis(1), basis(3))
    assert preserves(CNOT, FORM_K)
    assert preserves(CNOT, FORM_J)

    profiles = {}
    for k, j in product((0, 1), repeat=2):
        form = tuple((k & left) ^ (j & right) for left, right in zip(FORM_K, FORM_J))
        profiles[(k, j)] = form_rank(form)
    assert profiles == {(0, 0): 0, (0, 1): 2, (1, 0): 4, (1, 1): 4}

    diagonal_k: Vector = (1, 0, 0, 0, 0, 0)
    diagonal_j: Vector = (0, 0, 0, 0, 0, 1)
    vectors = tuple(product((0, 1), repeat=4))[1:]
    diagonal_solutions = 0
    for image_a, image_c in product(vectors, repeat=2):
        columns = (image_a, basis(1), image_c, add(basis(1), basis(3)))
        if rank(list(columns)) != 4:
            continue
        if preserves(columns, diagonal_k) and preserves(columns, diagonal_j):
            diagonal_solutions += 1
    assert diagonal_solutions == 0

    print("mixed-central CNOT columns=", CNOT)
    print("K form=", FORM_K, "J form=", FORM_J)
    print("central-character alternating ranks=", profiles)
    print("uncoupled block-diagonal completions=0")


if __name__ == "__main__":
    audit()
