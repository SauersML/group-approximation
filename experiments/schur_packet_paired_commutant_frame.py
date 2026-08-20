#!/usr/bin/env python3
"""Exact paired-word frame for the support packet commutant detector.

The source and coefficient copies of the packet each have four noncentral
Pauli coordinates (p1,p2,q1,q2).  We construct two fixed four-generator
subgroups of their product.  Their evaluated commutator ranks agree on the
three allowed J=-1 source characters and differ by one Pauli pair on 101.

The calculation is over F_2 and uses only the Python standard library.
"""
from __future__ import annotations

from itertools import product

Bit3 = tuple[int, int, int]
Bit4 = tuple[int, int, int, int]
Matrix4 = tuple[Bit4, Bit4, Bit4, Bit4]

ZERO3: Bit3 = (0, 0, 0)
CHARACTERS = tuple(product((0, 1), repeat=3))
ALLOWED = ((1, 0, 0), (1, 1, 0), (1, 1, 1))
FORBIDDEN = (1, 0, 1)
COEFFICIENT_PLUS = (0, 1, 1)
COEFFICIENT_MINUS = (1, 0, 1)
IDENTITY4: Matrix4 = tuple(
    tuple(int(row == column) for column in range(4)) for row in range(4)
)  # type: ignore[assignment]
PAIRS = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))

# Symbolic alternating form in the central basis (J,z_e,z_f).
SYMBOLIC = (
    (ZERO3, ZERO3, (1, 0, 0), (1, 1, 0)),
    (ZERO3, ZERO3, (0, 0, 1), ZERO3),
    ((1, 0, 0), (0, 0, 1), ZERO3, ZERO3),
    ((1, 1, 0), ZERO3, ZERO3, ZERO3),
)

# Rows give the coefficient-coordinate word paired with each source generator.
PLUS_WORDS: Matrix4 = (
    (1, 1, 0, 0),
    (0, 1, 0, 0),
    (0, 0, 1, 1),
    (0, 0, 0, 1),
)
MINUS_WORDS = IDENTITY4


def add(*vectors: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(sum(vector[index] for vector in vectors) & 1 for index in range(len(vectors[0])))


def dot(left: tuple[int, ...], right: tuple[int, ...]) -> int:
    return sum(a & b for a, b in zip(left, right)) & 1


def rank_f2(rows: tuple[tuple[int, ...], ...] | list[list[int]]) -> int:
    work = [list(row) for row in rows]
    pivot_row = 0
    if not work:
        return 0
    for column in range(len(work[0])):
        pivot = next(
            (row for row in range(pivot_row, len(work)) if work[row][column]),
            None,
        )
        if pivot is None:
            continue
        work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
        for row in range(len(work)):
            if row != pivot_row and work[row][column]:
                work[row] = [a ^ b for a, b in zip(work[row], work[pivot_row])]
        pivot_row += 1
    return pivot_row


def evaluated_packet_form(character: Bit3) -> Matrix4:
    return tuple(
        tuple(dot(character, SYMBOLIC[row][column]) for column in range(4))
        for row in range(4)
    )  # type: ignore[return-value]


def evaluated_frame_form(
    source_character: Bit3, coefficient_character: Bit3, coefficient_words: Matrix4
) -> Matrix4:
    source_form = evaluated_packet_form(source_character)
    coefficient_form = evaluated_packet_form(coefficient_character)
    return tuple(
        tuple(
            source_form[row][column]
            ^ sum(
                coefficient_words[row][left]
                & coefficient_form[left][right]
                & coefficient_words[column][right]
                for left in range(4)
                for right in range(4)
            )
            % 2
            for column in range(4)
        )
        for row in range(4)
    )  # type: ignore[return-value]


def symbolic_commutator_columns(coefficient_words: Matrix4) -> tuple[tuple[int, ...], ...]:
    columns = []
    for first, second in PAIRS:
        value: list[int] = []
        for words in (IDENTITY4, coefficient_words):
            central = ZERO3
            for left, right in product(range(4), repeat=2):
                if words[first][left] & words[second][right]:
                    central = add(central, SYMBOLIC[left][right])  # type: ignore[assignment]
            value.extend(central)
        columns.append(tuple(value))
    return tuple(columns)


def relation_kernel(columns: tuple[tuple[int, ...], ...]) -> set[tuple[int, ...]]:
    return {
        coefficients
        for coefficients in product((0, 1), repeat=6)
        if add(
            (0,) * 6,
            *(columns[index] for index, bit in enumerate(coefficients) if bit),
        )
        == (0,) * 6
    }


def wedge_image(matrix: Matrix4, pair: tuple[int, int]) -> tuple[int, ...]:
    first, second = pair
    return tuple(
        (matrix[first][left] & matrix[second][right])
        ^ (matrix[first][right] & matrix[second][left])
        for left, right in PAIRS
    )


def transformed_kernel(matrix: Matrix4, kernel: set[tuple[int, ...]]) -> set[tuple[int, ...]]:
    return {
        add(
            (0,) * 6,
            *(wedge_image(matrix, PAIRS[index]) for index, bit in enumerate(vector) if bit),
        )
        for vector in kernel
    }


def matrix_multiply(left: Matrix4, right: Matrix4) -> Matrix4:
    return tuple(
        tuple(sum(left[row][middle] & right[middle][column] for middle in range(4)) & 1 for column in range(4))
        for row in range(4)
    )  # type: ignore[return-value]


def transpose(matrix: Matrix4) -> Matrix4:
    return tuple(tuple(matrix[row][column] for row in range(4)) for column in range(4))  # type: ignore[return-value]


def pull_form(matrix: Matrix4, form: Matrix4) -> Matrix4:
    return matrix_multiply(matrix_multiply(matrix, form), transpose(matrix))


def audit() -> None:
    plus_forms = {
        character: evaluated_frame_form(character, COEFFICIENT_PLUS, PLUS_WORDS)
        for character in CHARACTERS
    }
    minus_forms = {
        character: evaluated_frame_form(character, COEFFICIENT_MINUS, MINUS_WORDS)
        for character in CHARACTERS
    }
    plus_profile = {character: rank_f2(form) for character, form in plus_forms.items()}
    minus_profile = {character: rank_f2(form) for character, form in minus_forms.items()}
    assert [plus_profile[x] for x in (*ALLOWED, FORBIDDEN)] == [2, 4, 2, 2]
    assert [minus_profile[x] for x in (*ALLOWED, FORBIDDEN)] == [2, 4, 2, 0]

    plus_columns = symbolic_commutator_columns(PLUS_WORDS)
    minus_columns = symbolic_commutator_columns(MINUS_WORDS)
    assert rank_f2(plus_columns) == rank_f2(minus_columns) == 3
    plus_kernel = relation_kernel(plus_columns)
    minus_kernel = relation_kernel(minus_columns)
    assert plus_kernel == minus_kernel

    isomorphisms = []
    for flat in product((0, 1), repeat=16):
        matrix: Matrix4 = tuple(
            tuple(flat[4 * row : 4 * row + 4]) for row in range(4)
        )  # type: ignore[assignment]
        if rank_f2(matrix) != 4:
            continue
        if transformed_kernel(matrix, plus_kernel) == minus_kernel:
            isomorphisms.append(matrix)
    assert len(isomorphisms) == 32

    patterns: set[tuple[tuple[Bit3, ...], ...]] = set()
    for matrix in isomorphisms:
        pattern = tuple(
            tuple(
                target
                for target in CHARACTERS
                if plus_forms[source] == pull_form(matrix, minus_forms[target])
            )
            for source in CHARACTERS
        )
        assert all(len(targets) == 1 for targets in pattern)
        forbidden_targets = pattern[CHARACTERS.index(FORBIDDEN)]
        assert forbidden_targets == ((0, 1, 1),)
        patterns.add(pattern)
    assert len(patterns) == 8

    print("paired frame generators (source word | coefficient word):")
    for source, coefficient in zip(IDENTITY4, PLUS_WORDS):
        print("  plus ", source, "|", coefficient)
    for source, coefficient in zip(IDENTITY4, MINUS_WORDS):
        print("  minus", source, "|", coefficient)
    print("rank profile on 100,110,111,101:")
    print("  plus ", [plus_profile[x] for x in (*ALLOWED, FORBIDDEN)])
    print("  minus", [minus_profile[x] for x in (*ALLOWED, FORBIDDEN)])
    print("symbolic commutator rank: 3 on both sides; relation kernels coincide")
    print("frame-group isomorphisms: 32; character-transport patterns: 8")
    print("every isomorphism transports source character 101 to 011")


if __name__ == "__main__":
    audit()
