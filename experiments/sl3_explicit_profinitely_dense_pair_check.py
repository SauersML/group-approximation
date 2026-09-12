#!/usr/bin/env python3
"""Exact transcription checks for the explicit SL_3(Z) thin pair.

This does not re-prove profinite density.  It verifies the published word
formulas, determinants, and the order-three outsider using integer arithmetic.
"""


def mul(left, right):
    return tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(3)) for j in range(3))
        for i in range(3)
    )


def det(matrix):
    a, b, c = matrix[0]
    d, e, f = matrix[1]
    g, h, i = matrix[2]
    return a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)


def inv(matrix):
    assert det(matrix) == 1
    a, b, c = matrix[0]
    d, e, f = matrix[1]
    g, h, i = matrix[2]
    return (
        (e * i - f * h, c * h - b * i, b * f - c * e),
        (f * g - d * i, a * i - c * g, c * d - a * f),
        (d * h - e * g, b * g - a * h, a * e - b * d),
    )


def product(*matrices):
    value = IDENTITY
    for matrix in matrices:
        value = mul(value, matrix)
    return value


IDENTITY = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
F1 = ((1, 122, 11), (0, 1, 0), (0, 0, 1))
F2 = ((1, 0, 0), (11, 1, 12), (0, 0, 1))
F3 = ((1, 0, 0), (0, 1, 0), (-10, 121, 1))

A = (
    (-176379047, 1936571625, -17817867),
    (-1941616205, 21318171799, -196142682),
    (10, -121, 1),
)
B = (
    (-40193888, -3684209, -44180039),
    (396162230, 36312596, 435450841),
    (3829559, 351021, 4209349),
)
R = ((0, -1, 0), (1, -1, 0), (0, 0, 1))

A_FROM_WORD = product(F2, F1, inv(F2), inv(F1), F2, inv(F1), inv(F3))
INNER_B = product(inv(F1), inv(F3), inv(F3), F2, inv(F3))
B_FROM_WORD = product(inv(F2), INNER_B, F2)

assert A_FROM_WORD == A
assert B_FROM_WORD == B
assert det(A) == det(B) == det(R) == 1
assert product(R, R, R) == IDENTITY
assert R != IDENTITY

print("verified: published words, determinants, and r^3=I")
