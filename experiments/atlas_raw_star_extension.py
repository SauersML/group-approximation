"""Audit inverse-transpose synchronization of the raw Pauli cut.

The finite calculation verifies that inverse-transpose is the outer
involution of GL_3(2), while exact Leavitt arithmetic verifies that the raw
involution is fixed by the transpose anti-involution.  These are the finite
facts behind adjoining a spatial star implementer to the atlas group.
"""

import collections
import itertools
import json
import sys

sys.path.insert(0, "experiments")

from atlas_raw_compressor_proper_infinite import raw_and_comb  # noqa: E402
from atlas_survivor_prefix_obstruction import (  # noqa: E402
    leavitt_is_zero,
    leavitt_star,
)
from atlas_two_chart_search import leavitt_add  # noqa: E402


def matrix(rows):
    return tuple(tuple(int(value) & 1 for value in row) for row in rows)


IDENTITY = matrix(((1, 0, 0), (0, 1, 0), (0, 0, 1)))


def multiply(left, right):
    return matrix(tuple(
        tuple(sum(left[i][k] * right[k][j] for k in range(3)) & 1
              for j in range(3))
        for i in range(3)
    ))


def transpose(value):
    return matrix(tuple(tuple(value[j][i] for j in range(3))
                        for i in range(3)))


def rank(value):
    rows = [sum(value[i][j] << j for j in range(3)) for i in range(3)]
    pivot = 0
    for column in range(3):
        selected = next((row for row in range(pivot, 3)
                         if (rows[row] >> column) & 1), None)
        if selected is None:
            continue
        rows[pivot], rows[selected] = rows[selected], rows[pivot]
        for row in range(3):
            if row != pivot and ((rows[row] >> column) & 1):
                rows[row] ^= rows[pivot]
        pivot += 1
    return pivot


def inverse(value):
    return INVERSES[value]


def theta(value):
    return transpose(inverse(value))


def element_order(value, product, identity, limit=32):
    running = identity
    for exponent in range(1, limit + 1):
        running = product(running, value)
        if running == identity:
            return exponent
    return None


GL3 = tuple(
    matrix(tuple(tuple(bits[3 * i + j] for j in range(3))
                 for i in range(3)))
    for bits in itertools.product((0, 1), repeat=9)
    if rank(matrix(tuple(tuple(bits[3 * i + j] for j in range(3))
                         for i in range(3)))) == 3
)

INVERSES = {
    value: next(candidate for candidate in GL3
                if multiply(value, candidate) == IDENTITY)
    for value in GL3
}


def semidirect_multiply(left, right):
    g, epsilon = left
    h, eta = right
    return (multiply(g, theta(h) if epsilon else h), epsilon ^ eta)


def main():
    theta_is_automorphism = all(
        theta(multiply(g, h)) == multiply(theta(g), theta(h))
        for g in GL3 for h in GL3
    )
    theta_is_involution = all(theta(theta(g)) == g for g in GL3)
    inner_implementers = []
    for candidate in GL3:
        candidate_inverse = inverse(candidate)
        if all(multiply(multiply(candidate, g), candidate_inverse) == theta(g)
               for g in GL3):
            inner_implementers.append(candidate)

    semidirect = tuple((g, epsilon) for g in GL3 for epsilon in (0, 1))
    semidirect_histogram = dict(sorted(collections.Counter(
        element_order(value, semidirect_multiply, (IDENTITY, 0))
        for value in semidirect).items()))

    raw, _ = raw_and_comb()
    raw_is_leavitt_self_adjoint = leavitt_is_zero(
        leavitt_add(leavitt_star(raw), raw))

    result = {
        "gl3_2_order": len(GL3),
        "inverse_transpose_is_automorphism": theta_is_automorphism,
        "inverse_transpose_is_involution": theta_is_involution,
        "inverse_transpose_inner_implementer_count": len(inner_implementers),
        "inverse_transpose_is_outer": not inner_implementers,
        "semidirect_order": len(semidirect),
        "semidirect_order_histogram": semidirect_histogram,
        "raw_is_fixed_by_leavitt_transpose": raw_is_leavitt_self_adjoint,
        "raw_cut_preserved_by_spatial_star_involution":
            raw_is_leavitt_self_adjoint and theta_is_involution,
        "with_central_raw_sign_finite_subgroup_order": 2 * len(semidirect),
    }
    if not all((
        result["gl3_2_order"] == 168,
        theta_is_automorphism,
        theta_is_involution,
        not inner_implementers,
        result["semidirect_order"] == 336,
        semidirect_histogram == {1: 1, 2: 49, 3: 56, 4: 42,
                                 6: 56, 7: 48, 8: 84},
        raw_is_leavitt_self_adjoint,
        result["with_central_raw_sign_finite_subgroup_order"] == 672,
    )):
        raise AssertionError(result)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
