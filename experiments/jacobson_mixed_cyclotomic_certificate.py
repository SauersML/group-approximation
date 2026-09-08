#!/usr/bin/env python3
"""Exact 12-dimensional mixed packet with both Jacobson braid defects < 2.

Arithmetic is in Q[z]/(1+z+...+z^6). Nonzero determinants of U+I
certify the strict operator-norm bound for the two exact unitaries U.
No numerical search result, rounding, or approximation is accepted as proof.
"""

from fractions import Fraction
from itertools import product
import json

import jacobson_two_braid_audit as binary


ZERO = (Fraction(0),) * 6
ONE = (Fraction(1),) + ZERO[1:]
Z = (Fraction(0), Fraction(1)) + ZERO[2:]


def scalar(value):
    return (Fraction(value),) + ZERO[1:]


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def neg(a):
    return tuple(-x for x in a)


def scale(a, coefficient):
    return tuple(x * coefficient for x in a)


def multiply(a, b):
    coeffs = [Fraction(0)] * 11
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    coeffs[i + j] += x * y
    for i in range(10, 5, -1):
        x = coeffs[i]
        if x:
            for j in range(6):
                coeffs[i - 6 + j] -= x
    return tuple(coeffs[:6])


ZPOW = [ONE]
for _ in range(6):
    ZPOW.append(multiply(ZPOW[-1], Z))


def automorphism(a, exponent):
    out = ZERO
    for i, coefficient in enumerate(a):
        out = add(out, scale(ZPOW[(i * exponent) % 7], coefficient))
    return out


def conjugate(a):
    return automorphism(a, 6)


def inverse(a):
    binary.require(a != ZERO, "Inversion of zero")
    other = ONE
    for k in range(2, 7):
        other = multiply(other, automorphism(a, k))
    norm = multiply(a, other)
    binary.require(norm[0] != 0 and all(x == 0 for x in norm[1:]),
                   "Cyclotomic norm is not a nonzero rational")
    return scale(other, 1 / norm[0])


def eye(n):
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]


def matrix_add(a, b):
    return [[add(x, y) for x, y in zip(row_a, row_b)]
            for row_a, row_b in zip(a, b)]


def matrix_scale(a, coefficient):
    return [[scale(x, coefficient) for x in row] for row in a]


def matmul(a, b):
    return [[sum_field(multiply(a[i][k], b[k][j]) for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def sum_field(elements):
    out = ZERO
    for element in elements:
        out = add(out, element)
    return out


def adjoint(a):
    return [[conjugate(a[j][i]) for j in range(len(a))] for i in range(len(a[0]))]


def tensor(a, b):
    return [[multiply(a[i][j], b[k][l])
             for j in range(len(a[0])) for l in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]


def trivial_plus(a):
    out = [[ZERO] * 4 for _ in range(4)]
    out[0][0] = ONE
    for i in range(3):
        for j in range(3):
            out[i + 1][j + 1] = a[i][j]
    return out


def determinant(a):
    a = [row[:] for row in a]
    out = ONE
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j] != ZERO), None)
        if pivot is None:
            return ZERO
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            out = neg(out)
        value = a[j][j]
        out = multiply(out, value)
        value_inverse = inverse(value)
        for i in range(j + 1, len(a)):
            if a[i][j] == ZERO:
                continue
            ratio = multiply(a[i][j], value_inverse)
            for k in range(j + 1, len(a)):
                a[i][k] = add(a[i][k], neg(multiply(ratio, a[j][k])))
            a[i][j] = ZERO
    return out


def exact_representation():
    one = binary.identity(3)
    group = sorted(a for a in product(range(8), repeat=3)
                   if len({binary.apply(a, v) for v in range(8)}) == 8)
    x = binary.swap(3, 0, 2)
    # A finite deterministic search specifies y; its full generated group
    # and every generator edge are independently checked below.
    y = next(a for a in group if a != one and binary.power(a, 3) == one
             and binary.power(binary.multiply(x, a), 7) == one
             and binary.power(binary.multiply(binary.multiply(binary.multiply(x, a), x),
                                               binary.power(a, 2)), 4) == one
             and len(binary.closure((x, a), 3)) == 168)
    gauss = sum_field(scale(ZPOW[k], 1 if k in (1, 2, 4) else -1)
                      for k in range(1, 7))
    binary.require(multiply(gauss, gauss) == scalar(-7), "Gauss identity failed")
    S = [[scale(multiply(gauss, add(ZPOW[(i*j) % 7], neg(ZPOW[(-i*j) % 7]))),
                Fraction(1, 7)) for j in (1, 2, 3)] for i in (1, 2, 3)]
    T = [[ZPOW[(4, 2, 1)[i]] if i == j else ZERO for j in range(3)] for i in range(3)]
    X, Y = S, matmul(S, T)
    for A in (X, Y):
        binary.require(matmul(adjoint(A), A) == eye(3), "Generator is not unitary")
    rep = {one: eye(3)}
    todo = [one]
    while todo:
        g = todo.pop()
        for a, A in ((x, X), (y, Y)):
            ag = binary.multiply(a, g)
            if ag not in rep:
                rep[ag] = matmul(A, rep[g])
                todo.append(ag)
    binary.require(set(rep) == set(group), "Generators do not reach all of GL_3(2)")
    for g in group:
        for a, A in ((x, X), (y, Y)):
            binary.require(rep[binary.multiply(a, g)] == matmul(A, rep[g]),
                           "Exact representation edge failed")
    return group, rep, x, y


def run():
    binary.require(multiply(ZPOW[6], Z) == ONE, "Seventh-root relation failed")
    binary.require(sum_field(ZPOW) == ZERO, "Cyclotomic relation failed")
    group, rep, x, y = exact_representation()
    one = binary.identity(3)
    K = [g for g in group if g[1] == 2 and all(not (g[j] & 2) for j in (0, 2))]
    sign = {g: -1 if g != one and binary.power(g, 2) == one else 1 for g in K}
    binary.require(len(K) == 6, "Wrong overlap group")
    for g in K:
        for h in K:
            binary.require(sign[binary.multiply(g, h)] == sign[g] * sign[h],
                           "The overlap sign is not a character")
    P = [[sum_field(scale(rep[g][i][j], Fraction(sign[g], 6)) for g in K)
          for j in range(3)] for i in range(3)]
    binary.require(adjoint(P) == P and matmul(P, P) == P, "Overlap cut is not a projection")
    binary.require(sum_field(P[i][i] for i in range(3)) == ONE, "Overlap cut has wrong rank")
    for g in K:
        binary.require(matmul(P, rep[g]) == matmul(rep[g], P), "Overlap cut does not commute")
    A = [[scalar(v) for v in row] for row in
         ((0, 1, 0, 0), (1, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0))]
    C = [[scalar(v) for v in row] for row in
         ((0, 0, 1, 0), (0, 1, 0, 0), (1, 0, 0, 0), (0, 0, 0, -1))]
    H = matrix_add(tensor(P, A), tensor(matrix_add(eye(3), matrix_scale(P, -1)), C))
    binary.require(adjoint(H) == H and matmul(H, H) == eye(12), "H is not an involution")
    b = binary.swap(3, 1, 2)
    d = binary.swap(3, 0, 2)
    B = tensor(rep[b], trivial_plus(rep[b]))
    D = tensor(eye(3), trivial_plus(rep[d]))
    mark = tensor(rep[binary.transvection(3, 0, 2)], eye(4))
    binary.require(mark != eye(12), "Mark was lost")
    binary.require(sum_field(mark[i][i] for i in range(12)) == scalar(-4),
                   "Mark does not have negative rank eight")
    determinants = []
    for actor in (B, D):
        V = matmul(H, actor)
        cube = matmul(matmul(V, V), V)
        det = determinant(matrix_add(cube, eye(12)))
        binary.require(det != ZERO, "A braid has norm defect two")
        determinants.append([str(coefficient) for coefficient in det])
    return {"format": "jacobson-mixed-cyclotomic-certificate-v1",
            "field": "Q[z]/(1+z+z^2+z^3+z^4+z^5+z^6), z=exp(2*pi*i/7)",
            "group_order": len(group), "exact_generator_edges_verified": 2 * len(group),
            "binary_generator_columns": {"x": list(x), "y": list(y)},
            "dimension": 12, "marked_negative_rank": 8,
            "det_braid_cube_plus_identity_coefficients": determinants,
            "both_operator_norm_braid_defects_strictly_below_two": True,
            "positive_all_dimensions_gap_proved": False,
            "exact_braid_relations_claimed": False,
            "non_mf_existence_proved": False}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
