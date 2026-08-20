#!/usr/bin/env python3
"""Search a six-generator completion of CNOT with unequal commutator labels.

Use three hyperbolic planes labelled K, J, and K+J.  Equivalently, preserve
simultaneously the two alternating forms with planes (a,b),(e,f) and
(c,d),(e,f).  We require b -> b and d -> b+d, then exhaust the remaining
four image vectors for a common invertible isometry of both forms.  That
block-diagonal attempt fails by radical preservation.  We then allow symbolic
K/J cross commutators and solve the invariant alternating-form equations for
low-weight CNOT completions.
"""
from __future__ import annotations

from itertools import product

Vector = tuple[int, ...]
Matrix = tuple[Vector, ...]
PAIRS_K = ((0, 1), (4, 5))
PAIRS_J = ((2, 3), (4, 5))
ALL_PAIRS = tuple((left, right) for left in range(6) for right in range(left + 1, 6))
ENGINEERED_COLUMNS: Matrix = (
    (0, 0, 1, 0, 1, 0),
    (0, 1, 0, 0, 0, 0),
    (1, 0, 0, 0, 0, 0),
    (0, 1, 0, 1, 0, 0),
    (1, 1, 1, 0, 0, 1),
    (1, 1, 1, 0, 0, 0),
)
ENGINEERED_K: Vector = (1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0)
ENGINEERED_J: Vector = (0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0)


def add(left: Vector, right: Vector) -> Vector:
    return tuple(a ^ b for a, b in zip(left, right))


def basis(index: int) -> Vector:
    return tuple(int(position == index) for position in range(6))


def alternating(vector: Vector, other: Vector, pairs: tuple[tuple[int, int], ...]) -> int:
    return sum(
        (vector[left] & other[right]) ^ (vector[right] & other[left])
        for left, right in pairs
    ) & 1


def label(vector: Vector, other: Vector) -> tuple[int, int]:
    return alternating(vector, other, PAIRS_K), alternating(vector, other, PAIRS_J)


def rank(vectors: list[Vector]) -> int:
    work = [list(vector) for vector in vectors]
    pivot = 0
    for column in range(6):
        row = next((row for row in range(pivot, len(work)) if work[row][column]), None)
        if row is None:
            continue
        work[pivot], work[row] = work[row], work[pivot]
        for other in range(len(work)):
            if other != pivot and work[other][column]:
                work[other] = [a ^ b for a, b in zip(work[other], work[pivot])]
        pivot += 1
    return pivot


def solve(rows: list[list[int]], values: list[int]) -> Vector | None:
    work = [row[:] + [value] for row, value in zip(rows, values)]
    pivot = 0
    pivots: list[int] = []
    for column in range(len(ALL_PAIRS)):
        row = next((row for row in range(pivot, len(work)) if work[row][column]), None)
        if row is None:
            continue
        work[pivot], work[row] = work[row], work[pivot]
        for other in range(len(work)):
            if other != pivot and work[other][column]:
                work[other] = [a ^ b for a, b in zip(work[other], work[pivot])]
        pivots.append(column)
        pivot += 1
    if any(not any(row[:-1]) and row[-1] for row in work):
        return None
    answer = [0] * len(ALL_PAIRS)
    for row, column in enumerate(pivots):
        answer[column] = work[row][-1]
    return tuple(answer)


def wedge(left: Vector, right: Vector) -> list[int]:
    return [
        (left[first] & right[second]) ^ (left[second] & right[first])
        for first, second in ALL_PAIRS
    ]


def square(vector: Vector) -> list[int]:
    return [vector[first] & vector[second] for first, second in ALL_PAIRS]


def invariant_form(columns: Matrix, fixed: dict[tuple[int, int], int]) -> Vector | None:
    rows: list[list[int]] = []
    values: list[int] = []
    for first, second in ALL_PAIRS:
        equation = wedge(columns[first], columns[second])
        equation[ALL_PAIRS.index((first, second))] ^= 1
        rows.append(equation)
        values.append(0)
    # The packet generators are involutions.  Preserving the alternating
    # form is insufficient in characteristic two: every image column must
    # also have trivial square in each central label.
    for column in columns:
        rows.append(square(column))
        values.append(0)
    for pair, value in fixed.items():
        equation = [0] * len(ALL_PAIRS)
        equation[ALL_PAIRS.index(pair)] = 1
        rows.append(equation)
        values.append(value)
    return solve(rows, values)


def form_rank(form: Vector) -> int:
    matrix = [[0] * 6 for _ in range(6)]
    for value, (left, right) in zip(form, ALL_PAIRS):
        matrix[left][right] = matrix[right][left] = value
    return rank([tuple(row) for row in matrix])


def audit() -> None:
    vectors = tuple(product((0, 1), repeat=6))
    source = [basis(index) for index in range(6)]
    target: list[Vector | None] = [None] * 6
    target[1] = basis(1)  # b -> b
    target[3] = add(basis(1), basis(3))  # d -> b d
    order = (0, 2, 4, 5)
    best: tuple[int, Matrix] | None = None
    solutions = 0

    def search(depth: int) -> None:
        nonlocal best, solutions
        if depth == len(order):
            columns = tuple(vector for vector in target if vector is not None)
            assert len(columns) == 6
            if rank(list(columns)) != 6:
                return
            solutions += 1
            weight = sum(sum(vector) for vector in columns)
            if best is None or weight < best[0]:
                best = weight, columns  # type: ignore[assignment]
            return

        index = order[depth]
        for candidate in vectors[1:]:
            assigned = [position for position, vector in enumerate(target) if vector is not None]
            if any(label(candidate, target[position]) != label(source[index], source[position]) for position in assigned):  # type: ignore[arg-type]
                continue
            partial = [vector for vector in target if vector is not None] + [candidate]
            if rank(partial) != len(partial):
                continue
            target[index] = candidate
            search(depth + 1)
            target[index] = None

    search(0)
    print(f"block-diagonal common CNOT completions={solutions}")
    print(f"block-diagonal minimum={best}")
    assert best is None
    print("block-diagonal obstruction: d is K-radical but b+d is not")

    # Engineer cross commutators instead.  Keep the four unspecified images
    # close to their basis vectors, allowing additions of b and d.
    choices: dict[int, tuple[Vector, ...]] = {}
    for index in (0, 2, 4, 5):
        choices[index] = tuple(
            add(add(basis(index), basis(1)) if use_b else basis(index), basis(3))
            if use_d
            else (add(basis(index), basis(1)) if use_b else basis(index))
            for use_b, use_d in product((0, 1), repeat=2)
        )

    engineered = None
    for images in product(*(choices[index] for index in (0, 2, 4, 5))):
        columns = [basis(index) for index in range(6)]
        columns[1] = basis(1)
        columns[3] = add(basis(1), basis(3))
        for index, image in zip((0, 2, 4, 5), images):
            columns[index] = image
        if rank(columns) != 6:
            continue
        matrix = tuple(columns)
        form_k = invariant_form(matrix, {(0, 1): 1, (2, 3): 0})
        if form_k is None:
            continue
        form_j = invariant_form(matrix, {(0, 1): 0, (2, 3): 1})
        if form_j is None:
            continue
        engineered = matrix, form_k, form_j
        break

    print(f"restricted shear completion={engineered}")
    assert engineered is None

    assert rank(list(ENGINEERED_COLUMNS)) == 6
    assert ENGINEERED_COLUMNS[1] == basis(1)
    assert ENGINEERED_COLUMNS[3] == add(basis(1), basis(3))
    assert invariant_form(ENGINEERED_COLUMNS, {(0, 1): 1, (2, 3): 0}) == ENGINEERED_K
    assert invariant_form(ENGINEERED_COLUMNS, {(0, 1): 0, (2, 3): 1}) == ENGINEERED_J
    profiles = {}
    for k, j in product((0, 1), repeat=2):
        form = tuple((k & left) ^ (j & right) for left, right in zip(ENGINEERED_K, ENGINEERED_J))
        profiles[(k, j)] = form_rank(form)
    print(f"exact engineered columns={ENGINEERED_COLUMNS}")
    print(f"K form={ENGINEERED_K}")
    print(f"J form={ENGINEERED_J}")
    print(f"central-character alternating ranks={profiles}")


if __name__ == "__main__":
    audit()
