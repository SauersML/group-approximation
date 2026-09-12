"""Compile the scalarized raw compressors into the two A8 atlas charts.

The raw swap and comb are printed as elementary words in ``EL_4(L)``.  The
depth-two prefix equivalence sends every rank-four transvection to a scalar
leaf transvection ``1 + alpha beta*`` in ``L^x``.  This script expresses each
such transvection as a word in the two explicit ``A8`` atlas factors.

Only the Steinberg identity

    [x_ij(a), x_jk(b)] = x_ik(ab)

and the thirty atlas roots from ``atlas_two_chart_search.q`` are used.  The
resulting words are verified by exact all-depth Leavitt reduction.  They are
the source-coordinate input needed for representation-type or spherical
compression of the raw two-child packet.
"""

import json
import sys

sys.path.insert(0, "experiments")

from atlas_raw_compressor_proper_infinite import raw_and_comb  # noqa: E402
from atlas_survivor_prefix_obstruction import leavitt_is_zero  # noqa: E402
from atlas_two_chart_search import (  # noqa: E402
    commutator,
    leavitt_chart_element,
    leavitt_mul,
    matrix_key,
    product,
    q,
)


ONE = {((), ()): 1}
FOUR_LEAVES = ((0, 0), (0, 1), (1, 0), (1, 1))
GAMMA = ((0, 0), (0, 1), (1,))


def coeff_s(bit):
    return {((bit,), ()): 1}


def coeff_t(bit):
    return {((), (bit,)): 1}


def coeff_add(*values):
    result = {}
    for value in values:
        for monomial in value:
            if monomial in result:
                del result[monomial]
            else:
                result[monomial] = 1
    return result


def evaluate_source_word(word):
    value = ONE
    for factor, matrix in word:
        value = leavitt_mul(value, leavitt_chart_element(factor, matrix))
    return value


def assert_leavitt_equal(left, right, message):
    if not leavitt_is_zero(coeff_add(left, right)):
        raise AssertionError(message)


def other_index(i, j):
    return next(k for k in (1, 2, 3) if k != i and k != j)


def root_coefficient_word(i, j, atoms):
    """Compile x_ij(product(atoms)); indices are one-based."""
    if i == j:
        raise ValueError("root indices must differ")
    atoms = tuple(atoms)
    if not atoms:
        return q(i, j, "1")
    if len(atoms) == 1:
        return q(i, j, atoms[0])
    k = other_index(i, j)
    return commutator(
        root_coefficient_word(i, k, atoms[:-1]),
        root_coefficient_word(k, j, atoms[-1:]),
    )


def base_and_suffix(path):
    path = tuple(path)
    matches = [
        (index + 1, path[len(base):])
        for index, base in enumerate(GAMMA)
        if path[:len(base)] == base
    ]
    if len(matches) != 1:
        raise AssertionError("path does not have a unique atlas base leaf")
    return matches[0]


def cross_base_transvection(alpha, beta):
    """Compile 1+alpha beta* when the paths have different base leaves."""
    i, left_suffix = base_and_suffix(alpha)
    j, right_suffix = base_and_suffix(beta)
    if i == j:
        raise ValueError("expected different base leaves")
    atoms = tuple("e" if bit == 0 else "f" for bit in left_suffix)
    atoms += tuple("E" if bit == 0 else "F"
                   for bit in reversed(right_suffix))
    return root_coefficient_word(i, j, atoms)


def scalar_transvection_word(alpha, beta):
    """Compile the scalar prefix transvection 1+alpha beta*."""
    i, _ = base_and_suffix(alpha)
    j, _ = base_and_suffix(beta)
    if i != j:
        word = cross_base_transvection(alpha, beta)
    else:
        k = next(index for index in (1, 2, 3) if index != i)
        middle = GAMMA[k - 1]
        word = commutator(
            cross_base_transvection(alpha, middle),
            cross_base_transvection(middle, beta),
        )
    target = coeff_add(ONE, {(tuple(alpha), tuple(beta)): 1})
    assert_leavitt_equal(
        evaluate_source_word(word), target,
        "compiled scalar transvection has the wrong Leavitt value",
    )
    return word


def scalarized_rank_four_transvection(row, column, coefficient):
    """Compile Theta_C(x_row,column(coefficient))."""
    word = []
    for left, right in sorted(coefficient):
        alpha = FOUR_LEAVES[row] + tuple(left)
        beta = FOUR_LEAVES[column] + tuple(right)
        word = product(word, scalar_transvection_word(alpha, beta))
    return word


def raw_source_word():
    return product(
        scalarized_rank_four_transvection(0, 3, coeff_s(1)),
        scalarized_rank_four_transvection(3, 0, coeff_t(1)),
        scalarized_rank_four_transvection(0, 3, coeff_s(1)),
    )


def compressor_piece_source_word(index):
    return product(
        scalarized_rank_four_transvection(
            3, index, coeff_add(coeff_t(0), ONE)),
        scalarized_rank_four_transvection(index, 3, ONE),
        scalarized_rank_four_transvection(
            3, index, coeff_add(coeff_s(0), ONE)),
        scalarized_rank_four_transvection(index, 3, coeff_t(0)),
    )


def comb_source_word():
    return product(*(compressor_piece_source_word(index)
                     for index in (2, 1, 0)))


def encode_word(word):
    return [
        {
            "factor": factor,
            "matrix_f2_hex": matrix_key(matrix).hex(),
        }
        for factor, matrix in word
    ]


def main():
    raw_target, comb_target = raw_and_comb()
    raw_word = raw_source_word()
    comb_word = comb_source_word()

    assert_leavitt_equal(
        evaluate_source_word(raw_word), raw_target,
        "raw source word does not evaluate to the scalarized raw swap",
    )
    assert_leavitt_equal(
        evaluate_source_word(comb_word), comb_target,
        "comb source word does not evaluate to the scalarized compressor",
    )

    print(json.dumps({
        "compiler": "Steinberg commutators through the thirty atlas roots",
        "four_leaf_code": ["00", "01", "10", "11"],
        "raw_source_syllables": len(raw_word),
        "comb_source_syllables": len(comb_word),
        "raw_distinct_factor_elements": len({
            (factor, matrix_key(matrix)) for factor, matrix in raw_word
        }),
        "comb_distinct_factor_elements": len({
            (factor, matrix_key(matrix)) for factor, matrix in comb_word
        }),
        "verified": [
            "raw source word evaluates to scalarized raw swap",
            "comb source word evaluates to scalarized comb compressor",
        ],
        "raw_source_word": encode_word(raw_word),
        "comb_source_word": encode_word(comb_word),
    }, indent=2))


if __name__ == "__main__":
    main()
