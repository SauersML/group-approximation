#!/usr/bin/env python3
"""Exact M_4(Q[F_4]) audit of the one-marginal signed-Hecke escape cell."""
from __future__ import annotations

import json
from fractions import Fraction

D = 4
Word = tuple[int, ...]
Scalar = dict[Word, Fraction]
Matrix = list[list[Scalar]]


def reduce_word(word: Word) -> Word:
    stack: list[int] = []
    for letter in word:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def scalar_add(left: Scalar, right: Scalar) -> Scalar:
    result = dict(left)
    for word, coefficient in right.items():
        result[word] = result.get(word, Fraction()) + coefficient
        if not result[word]:
            del result[word]
    return result


def scalar_mul(left: Scalar, right: Scalar) -> Scalar:
    result: Scalar = {}
    for first, a in left.items():
        for second, b in right.items():
            word = reduce_word(first + second)
            result[word] = result.get(word, Fraction()) + a * b
    return {word: coefficient for word, coefficient in result.items() if coefficient}


def scalar_scale(value: Scalar, coefficient: Fraction) -> Scalar:
    return {word: coefficient * entry for word, entry in value.items() if coefficient * entry}


def scalar_star(value: Scalar) -> Scalar:
    return {tuple(-letter for letter in reversed(word)): coefficient for word, coefficient in value.items()}


def zero_matrix() -> Matrix:
    return [[{} for _ in range(D)] for _ in range(D)]


def matrix_add(left: Matrix, right: Matrix) -> Matrix:
    return [[scalar_add(left[i][j], right[i][j]) for j in range(D)] for i in range(D)]


def matrix_scale(value: Matrix, coefficient: Fraction) -> Matrix:
    return [[scalar_scale(value[i][j], coefficient) for j in range(D)] for i in range(D)]


def matrix_mul(left: Matrix, right: Matrix) -> Matrix:
    result = zero_matrix()
    for i in range(D):
        for j in range(D):
            for k in range(D):
                result[i][j] = scalar_add(result[i][j], scalar_mul(left[i][k], right[k][j]))
    return result


def matrix_star(value: Matrix) -> Matrix:
    return [[scalar_star(value[j][i]) for j in range(D)] for i in range(D)]


def matrix_unit(i: int, j: int, coefficient: Fraction = Fraction(1)) -> Matrix:
    result = zero_matrix()
    result[i][j] = {(): coefficient}
    return result


def identity() -> Matrix:
    result = zero_matrix()
    for i in range(D):
        result[i][i] = {(): Fraction(1)}
    return result


def word_label(word: Word) -> str:
    if not word:
        return "1"
    return " ".join(f"h{abs(letter)}" + ("^-1" if letter < 0 else "") for letter in word)


def main() -> None:
    half = Fraction(1, 2)
    f0 = matrix_scale(
        matrix_add(matrix_add(matrix_unit(0, 0), matrix_unit(1, 1)),
                   matrix_add(matrix_unit(0, 1), matrix_unit(1, 0))),
        half,
    )
    f1 = matrix_scale(
        matrix_add(matrix_add(matrix_unit(0, 0), matrix_unit(1, 1)),
                   matrix_scale(matrix_add(matrix_unit(0, 1), matrix_unit(1, 0)), -1)),
        half,
    )
    projections = [f0, f1, matrix_unit(2, 2), matrix_unit(3, 3)]

    w = zero_matrix()
    for i in range(D):
        w[i][i] = {(i + 1,): Fraction(1)}
    w_star = matrix_star(w)
    escaped = [matrix_mul(matrix_mul(w, projection), w_star) for projection in projections]

    signs = (1, 1, -1, -1)
    signed_sum = zero_matrix()
    for sign, projection in zip(signs, escaped):
        signed_sum = matrix_add(signed_sum, matrix_scale(projection, sign))
    d = matrix_add(matrix_add(matrix_unit(0, 0), matrix_unit(1, 1)),
                   matrix_scale(matrix_add(matrix_unit(2, 2), matrix_unit(3, 3)), -1))

    checks = {
        "W_is_unitary": matrix_mul(w_star, w) == identity() and matrix_mul(w, w_star) == identity(),
        "projections_are_self_adjoint": all(matrix_star(p) == p for p in escaped),
        "projections_are_idempotent": all(matrix_mul(p, p) == p for p in escaped),
        "projections_are_orthogonal": all(
            matrix_mul(escaped[i], escaped[j]) == zero_matrix()
            for i in range(D) for j in range(D) if i != j
        ),
        "projections_sum_to_identity": sum_matrices(escaped) == identity(),
        "signed_marginal_is_fixed": signed_sum == d,
    }
    if not all(checks.values()):
        raise AssertionError(checks)

    supports = []
    for projection in escaped:
        words = sorted({word for row in projection for entry in row for word in entry})
        supports.append([word_label(word) for word in words])
    nonroot = [any(word for row in projection for entry in row for word in entry) for projection in escaped]

    print(json.dumps({
        "dimension": D,
        "signs": signs,
        "checks": checks,
        "projection_free_word_supports": supports,
        "projection_escapes_root_block": nonroot,
    }, indent=2, sort_keys=True))


def sum_matrices(values: list[Matrix]) -> Matrix:
    result = zero_matrix()
    for value in values:
        result = matrix_add(result, value)
    return result


if __name__ == "__main__":
    main()
