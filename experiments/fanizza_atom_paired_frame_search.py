#!/usr/bin/env python3
"""Search a universal core-plus-Schur paired frame for every Fanizza bad atom.

For a forbidden atom, constant row/column operations put its Schur gate in
identity form while retaining the last coordinate as the named relative
Pauli pair.  We adjoin one baseline pivot, restrict to that 2-by-2 symbolic
submatrix, and test the same plus/minus word shears used by the support packet.

The finite test asks whether the plus and minus four-generator frames have the
same symbolic relation kernel and whether a coefficient character makes the
plus frame carry one Pauli while the stationary minus frame cancels.
"""
from __future__ import annotations

from itertools import product

from fanizza_fixed_predicate_rank_compiler import (
    Affine,
    BitTuple,
    best_compiler,
    evaluate_affine,
    evaluate_matrix,
    solve_f2,
)

BitVector = tuple[int, ...]
Bit4 = tuple[int, int, int, int]
Matrix4 = tuple[Bit4, Bit4, Bit4, Bit4]
PAIRS = ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
IDENTITY4: Matrix4 = tuple(
    tuple(int(row == column) for column in range(4)) for row in range(4)
)  # type: ignore[assignment]
PLUS_WORDS: Matrix4 = (
    (1, 1, 0, 0),
    (0, 1, 0, 0),
    (0, 0, 1, 1),
    (0, 0, 0, 1),
)


def dot(left: BitVector, right: BitVector) -> int:
    return sum(a & b for a, b in zip(left, right)) & 1


def add_vectors(*vectors: BitVector) -> BitVector:
    if not vectors:
        return ()
    return tuple(sum(vector[index] for vector in vectors) & 1 for index in range(len(vectors[0])))


def affine_vector(form: Affine) -> BitVector:
    return (form[0],) + form[1]


def matrix_multiply(left: list[list[int]], right: list[list[int]]) -> list[list[int]]:
    return [
        [
            sum(left[row][middle] & right[middle][column] for middle in range(len(right))) & 1
            for column in range(len(right[0]))
        ]
        for row in range(len(left))
    ]


def inverse_f2(matrix: list[list[int]]) -> list[list[int]]:
    size = len(matrix)
    columns = []
    for column in range(size):
        unit = [int(row == column) for row in range(size)]
        columns.append(solve_f2(matrix, unit))
    return [[columns[column][row] for column in range(size)] for row in range(size)]


def transform_affine(
    left: list[list[int]], matrix: list[list[Affine]], right: list[list[int]]
) -> list[list[Affine]]:
    arity = len(matrix[0][0][1])
    size = len(matrix)
    output = [[(0, (0,) * arity) for _ in range(size)] for _ in range(size)]
    for row in range(size):
        for column in range(size):
            terms = []
            for first in range(size):
                for second in range(size):
                    if left[row][first] & right[second][column]:
                        terms.append(affine_vector(matrix[first][second]))
            value = add_vectors((0,) * (arity + 1), *terms)
            output[row][column] = (value[0], value[1:])
    return output


def atom_normal_form(matrix: list[list[Affine]], atom: BitTuple) -> list[list[Affine]]:
    size = len(matrix)
    baseline = size - 1
    evaluated = evaluate_matrix(matrix, atom)
    leading = [row[:baseline] for row in evaluated[:baseline]]
    right_vector = [evaluated[row][baseline] for row in range(baseline)]
    bottom = evaluated[baseline][:baseline]
    alpha = solve_f2(leading, right_vector)
    leading_transpose = [
        [leading[row][column] for row in range(baseline)] for column in range(baseline)
    ]
    beta = solve_f2(leading_transpose, bottom)

    row_clear = [[int(row == column) for column in range(size)] for row in range(size)]
    column_clear = [[int(row == column) for column in range(size)] for row in range(size)]
    for column, bit in enumerate(beta):
        row_clear[baseline][column] = bit
    for row, bit in enumerate(alpha):
        column_clear[row][baseline] = bit

    normalize = [[0 for _ in range(size)] for _ in range(size)]
    leading_inverse = inverse_f2(leading)
    for row in range(baseline):
        for column in range(baseline):
            normalize[row][column] = leading_inverse[row][column]
    normalize[baseline][baseline] = 1
    left = matrix_multiply(normalize, row_clear)
    transformed = transform_affine(left, matrix, column_clear)
    assert evaluate_matrix(transformed, atom) == [
        [int(row == column) for column in range(size)] for row in range(size)
    ]
    return transformed


def alternating_form(block: list[list[Affine]]) -> tuple[tuple[BitVector, ...], ...]:
    zero = (0,) * (len(block[0][0][1]) + 1)
    return (
        (zero, zero, affine_vector(block[0][0]), affine_vector(block[0][1])),
        (zero, zero, affine_vector(block[1][0]), affine_vector(block[1][1])),
        (affine_vector(block[0][0]), affine_vector(block[1][0]), zero, zero),
        (affine_vector(block[0][1]), affine_vector(block[1][1]), zero, zero),
    )


def frame_columns(
    symbolic: tuple[tuple[BitVector, ...], ...], words: Matrix4
) -> tuple[BitVector, ...]:
    center_size = len(symbolic[0][0])
    columns = []
    for first, second in PAIRS:
        coefficient = (0,) * center_size
        for left, right in product(range(4), repeat=2):
            if words[first][left] & words[second][right]:
                coefficient = add_vectors(coefficient, symbolic[left][right])
        columns.append(coefficient)
    return tuple(columns)


def combined_columns(
    symbolic: tuple[tuple[BitVector, ...], ...], words: Matrix4
) -> tuple[BitVector, ...]:
    source = frame_columns(symbolic, IDENTITY4)
    coefficient = frame_columns(symbolic, words)
    return tuple(left + right for left, right in zip(source, coefficient))


def kernel_code(columns: tuple[BitVector, ...]) -> int:
    code = 0
    for index, bits in enumerate(product((0, 1), repeat=6)):
        value = add_vectors(
            (0,) * len(columns[0]),
            *(column for bit, column in zip(bits, columns) if bit),
        )
        if not any(value):
            code |= 1 << index
    return code


def rank_f2(rows: list[list[int]]) -> int:
    work = [row[:] for row in rows]
    rank = 0
    for column in range(len(work[0]) if work else 0):
        pivot = next((row for row in range(rank, len(work)) if work[row][column]), None)
        if pivot is None:
            continue
        work[rank], work[pivot] = work[pivot], work[rank]
        for row in range(len(work)):
            if row != rank and work[row][column]:
                work[row] = [a ^ b for a, b in zip(work[row], work[rank])]
        rank += 1
    return rank


def evaluated_frame_matrix(
    symbolic: tuple[tuple[BitVector, ...], ...],
    source_character: BitVector,
    coefficient_character: BitVector,
    words: Matrix4,
) -> list[list[int]]:
    matrix = []
    for row in range(4):
        matrix.append(
            [
                dot(source_character, symbolic[row][column])
                ^ sum(
                    words[row][left]
                    & dot(coefficient_character, symbolic[left][right])
                    & words[column][right]
                    for left in range(4)
                    for right in range(4)
                )
                % 2
                for column in range(4)
            ]
        )
    return matrix


def evaluated_frame_rank(
    symbolic: tuple[tuple[BitVector, ...], ...],
    source_character: BitVector,
    coefficient_character: BitVector,
    words: Matrix4,
) -> int:
    return rank_f2(
        evaluated_frame_matrix(symbolic, source_character, coefficient_character, words)
    )


def predicate_menu():
    a123 = {(1, 0, 0), (0, 1, 0), (0, 0, 1), (1, 1, 0), (1, 1, 1)}
    a456 = {(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)}
    return (
        ("conjunction-equality", 3, lambda x: bool(x[1] and (x[0] ^ x[2]))),
        ("conjunction-graph", 3, lambda x: bool(x[0] ^ (x[1] & x[2]))),
        (
            "conditional-three-projection-partition",
            6,
            lambda x: x[:3] in a123 and x[3:] in a456,
        ),
    )


def audit() -> None:
    total_atoms = 0
    solved_atoms = 0
    for name, arity, predicate in predicate_menu():
        _, _, matrix = best_compiler(arity, predicate)
        cube = tuple(product((0, 1), repeat=arity))
        full_characters = tuple(product((0, 1), repeat=arity + 1))
        for atom in cube:
            if not predicate(atom):
                continue
            total_atoms += 1
            transformed = atom_normal_form(matrix, atom)
            last = len(matrix) - 1
            atom_witnesses = []
            for core in range(last):
                block = [
                    [transformed[row][column] for column in (core, last)]
                    for row in (core, last)
                ]
                symbolic = alternating_form(block)
                if kernel_code(combined_columns(symbolic, PLUS_WORDS)) != kernel_code(
                    combined_columns(symbolic, IDENTITY4)
                ):
                    continue
                # This stronger equality is what lets the edge isomorphism fix
                # the entire source selector center: the coefficient-frame
                # commutator map has the same relations on both sides.
                if kernel_code(frame_columns(symbolic, PLUS_WORDS)) != kernel_code(
                    frame_columns(symbolic, IDENTITY4)
                ):
                    continue
                source_character = (1,) + atom
                minus_rank = evaluated_frame_rank(
                    symbolic, source_character, source_character, IDENTITY4
                )
                assert minus_rank == 0
                for coefficient_character in full_characters:
                    plus_rank = evaluated_frame_rank(
                        symbolic, source_character, coefficient_character, PLUS_WORDS
                    )
                    if plus_rank == 2:
                        atom_witnesses.append((core, coefficient_character))
            if atom_witnesses:
                solved_atoms += 1
                core, coefficient_character = atom_witnesses[0]
                block = [
                    [transformed[row][column] for column in (core, last)]
                    for row in (core, last)
                ]
                symbolic = alternating_form(block)
                plus_matrix = evaluated_frame_matrix(
                    symbolic, (1,) + atom, coefficient_character, PLUS_WORDS
                )
                same_source_targets = []
                for target_coefficient in full_characters:
                    target_matrix = evaluated_frame_matrix(
                        symbolic,
                        (1,) + atom,
                        target_coefficient,
                        IDENTITY4,
                    )
                    if target_matrix == plus_matrix:
                        same_source_targets.append(((1,) + atom, target_coefficient))
                print(
                    f"{name} atom={atom}: witness={(core, coefficient_character)} "
                    f"same-source-targets={same_source_targets[:2]}"
                )
            else:
                print(f"{name} atom={atom}: NO WITNESS")
    print(f"forbidden atoms solved={solved_atoms}/{total_atoms}")


if __name__ == "__main__":
    audit()
