#!/usr/bin/env python3
"""Search bounded Laurent words for a nonzero common-lift obstruction.

The search is deliberately exact.  It works in EL_3(F_2[x,x^{-1}]),
matches a conjugate of e_12(x^{-1}) against a polynomial elementary word,
lifts both words canonically to Z/4, and tests the resulting first-order
error modulo the image of Ad(gamma)-1 on sl_3(F_2[x,x^{-1}]/F_2[x]).

This is a bounded falsification tool for Theorem 8 of
notes/FALSE_CYCLOTOMIC_FIXED_ORBIT_FORMULA.md, not a proof that a surviving
bounded word remains nonzero in the untruncated deformation quotient.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Iterable


Poly = dict[int, int]
Matrix = tuple[tuple[Poly, ...], ...]
Letter = tuple[int, int, int]
Word = tuple[Letter, ...]


def poly_add(left: Poly, right: Poly, modulus: int) -> Poly:
    result = left.copy()
    for exponent, coefficient in right.items():
        result[exponent] = (result.get(exponent, 0) + coefficient) % modulus
        if result[exponent] == 0:
            del result[exponent]
    return result


def poly_mul(left: Poly, right: Poly, modulus: int) -> Poly:
    result: Poly = {}
    for left_exponent, left_coefficient in left.items():
        for right_exponent, right_coefficient in right.items():
            exponent = left_exponent + right_exponent
            result[exponent] = (
                result.get(exponent, 0) + left_coefficient * right_coefficient
            ) % modulus
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def identity(size: int = 3) -> Matrix:
    return tuple(
        tuple(({0: 1} if row == column else {}) for column in range(size))
        for row in range(size)
    )


def elementary(letter: Letter, modulus: int, inverse: bool = False) -> Matrix:
    row, column, exponent = letter
    result = [[entry.copy() for entry in matrix_row] for matrix_row in identity()]
    result[row][column] = {exponent: ((-1 if inverse else 1) % modulus)}
    return tuple(tuple(entry for entry in matrix_row) for matrix_row in result)


def matrix_mul(left: Matrix, right: Matrix, modulus: int) -> Matrix:
    size = len(left)
    result = [[{} for _ in range(size)] for _ in range(size)]
    for row, middle, column in product(range(size), repeat=3):
        result[row][column] = poly_add(
            result[row][column],
            poly_mul(left[row][middle], right[middle][column], modulus),
            modulus,
        )
    return tuple(tuple(entry for entry in matrix_row) for matrix_row in result)


def evaluate_word(word: Word, modulus: int, inverse: bool = False) -> Matrix:
    result = identity()
    letters: Iterable[Letter] = reversed(word) if inverse else word
    for letter in letters:
        result = matrix_mul(result, elementary(letter, modulus, inverse), modulus)
    return result


def matrix_key(matrix: Matrix) -> tuple[tuple[tuple[int, int], ...], ...]:
    return tuple(tuple(sorted(entry.items())) for row in matrix for entry in row)


def conjugate(matrix: Matrix, inverse: Matrix, target: Matrix, modulus: int) -> Matrix:
    return matrix_mul(matrix_mul(inverse, target, modulus), matrix, modulus)


def first_order_error(conjugator: Word, polynomial_stabilizer: Word) -> Matrix | None:
    modulus = 4
    g = evaluate_word(conjugator, modulus)
    g_inverse = evaluate_word(conjugator, modulus, inverse=True)
    h = elementary((0, 1, -1), modulus)
    gamma_inverse = evaluate_word(polynomial_stabilizer, modulus, inverse=True)
    error = matrix_mul(matrix_mul(matrix_mul(g_inverse, h, modulus), g, modulus), gamma_inverse, modulus)
    delta = [[{} for _ in range(3)] for _ in range(3)]
    for row, column in product(range(3), repeat=2):
        entry = error[row][column].copy()
        if row == column:
            entry = poly_add(entry, {0: -1 % modulus}, modulus)
        if any(coefficient % 2 for coefficient in entry.values()):
            return None
        delta[row][column] = {
            exponent: (coefficient // 2) % 2
            for exponent, coefficient in entry.items()
            if (coefficient // 2) % 2
        }
    return tuple(tuple(entry for entry in matrix_row) for matrix_row in delta)


SL3_BASIS = tuple(
    ((row, column),)
    for row, column in product(range(3), repeat=2)
    if row != column
) + (((0, 0), (1, 1)), ((1, 1), (2, 2)))


def negative_vector(matrix: Matrix, depth: int) -> int:
    vector = 0
    for row, column in product(range(3), repeat=2):
        for exponent, coefficient in matrix[row][column].items():
            if -depth <= exponent < 0 and coefficient % 2:
                bit = (row * 3 + column) * depth + (-exponent - 1)
                vector ^= 1 << bit
    return vector


def adjoint_columns(gamma: Matrix, gamma_inverse: Matrix, depth: int) -> list[int]:
    columns: list[int] = []
    for exponent in range(-depth, 0):
        for support in SL3_BASIS:
            tangent = [[{} for _ in range(3)] for _ in range(3)]
            for row, column in support:
                tangent[row][column] = {exponent: 1}
            tangent_matrix = tuple(tuple(entry for entry in row) for row in tangent)
            image = matrix_mul(matrix_mul(gamma, tangent_matrix, 2), gamma_inverse, 2)
            difference = tuple(
                tuple(poly_add(image[row][column], tangent_matrix[row][column], 2) for column in range(3))
                for row in range(3)
            )
            columns.append(negative_vector(difference, depth))
    return columns


def lies_in_span(target: int, columns: Iterable[int]) -> bool:
    pivots: dict[int, int] = {}
    for column in columns:
        while column:
            pivot = column.bit_length() - 1
            if pivot in pivots:
                column ^= pivots[pivot]
            else:
                pivots[pivot] = column
                break
    while target:
        pivot = target.bit_length() - 1
        if pivot not in pivots:
            return False
        target ^= pivots[pivot]
    return True


@dataclass(frozen=True)
class Candidate:
    conjugator: Word
    stabilizer: Word
    delta: Matrix
    membership_by_depth: tuple[bool, ...]


def breadth_first_words(generators: tuple[Letter, ...], max_depth: int) -> dict[tuple, Word]:
    states = {matrix_key(identity()): ()}
    frontier: list[tuple[Matrix, Word]] = [(identity(), ())]
    for _ in range(max_depth):
        next_frontier: list[tuple[Matrix, Word]] = []
        for matrix, word in frontier:
            for letter in generators:
                new_matrix = matrix_mul(matrix, elementary(letter, 2), 2)
                key = matrix_key(new_matrix)
                if key in states:
                    continue
                new_word = word + (letter,)
                states[key] = new_word
                next_frontier.append((new_matrix, new_word))
        frontier = next_frontier
    return states


def main() -> None:
    pairs = tuple((row, column) for row, column in product(range(3), repeat=2) if row != column)
    polynomial_generators = tuple((row, column, exponent) for row, column in pairs for exponent in range(3))
    polynomial_states = breadth_first_words(polynomial_generators, 4)
    laurent_generators = tuple((row, column, exponent) for row, column in pairs for exponent in range(-2, 3))
    laurent_states = breadth_first_words(laurent_generators, 3)
    h = elementary((0, 1, -1), 2)
    depths = (3, 5, 8, 12)
    fixed_count = 0
    candidates: list[Candidate] = []
    for conjugator in laurent_states.values():
        if not conjugator:
            continue
        g = evaluate_word(conjugator, 2)
        g_inverse = evaluate_word(conjugator, 2, inverse=True)
        gamma = conjugate(g, g_inverse, h, 2)
        stabilizer = polynomial_states.get(matrix_key(gamma))
        if stabilizer is None:
            continue
        fixed_count += 1
        delta = first_order_error(conjugator, stabilizer)
        if delta is None or negative_vector(delta, max(depths)) == 0:
            continue
        gamma_inverse = evaluate_word(stabilizer, 2, inverse=True)
        memberships = tuple(
            lies_in_span(negative_vector(delta, depth), adjoint_columns(gamma, gamma_inverse, depth))
            for depth in depths
        )
        if not memberships[-1]:
            candidates.append(Candidate(conjugator, stabilizer, delta, memberships))
    print(f"polynomial states: {len(polynomial_states)}")
    print(f"Laurent states: {len(laurent_states)}")
    print(f"matched fixed cosets: {fixed_count}")
    print(f"truncated obstruction candidates: {len(candidates)}")
    for candidate in candidates[:20]:
        print("g =", candidate.conjugator)
        print("gamma =", candidate.stabilizer)
        print("membership =", dict(zip(depths, candidate.membership_by_depth)))
        print("Delta =", [[sorted(entry.items()) for entry in row] for row in candidate.delta])


if __name__ == "__main__":
    main()
