"""Construct and verify an explicit one-transverse-chart atlas relation.

The first chart and the aligned rank-three subgroup of the second chart
already contain all scalar root elements.  The scalar Weyl word swapping
coordinates 1 and 2 therefore conjugates the first-chart root x_12(f) to
the transverse second-chart root x_21(f).
"""

import json

import numpy as np

from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_interior_single_bridge import aligned_matrix, aligned_value, lies_in_h
from atlas_two_chart_search import (
    I4,
    commutator,
    gf2_inv,
    inverse,
    leavitt_chart_element,
    leavitt_is_one,
    leavitt_mul,
    matrix_key,
    product,
    q,
)


ONE = {((), ()): 1}


def evaluate_word(word):
    value = ONE
    for factor, matrix in word:
        value = leavitt_mul(value, leavitt_chart_element(factor, matrix))
    return value


def encode_word(word):
    return [
        {"factor": factor, "matrix_f2_hex": matrix_key(matrix).hex()}
        for factor, matrix in word
    ]


def run():
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)

    scalar_x12 = commutator(q(1, 3, "1"), q(3, 2, "1"))
    scalar_x21 = commutator(q(2, 3, "1"), q(3, 1, "1"))
    weyl12 = product(scalar_x12, scalar_x21, scalar_x12)
    first_chart_root = q(1, 2, "f")
    second_chart_root = q(2, 1, "f")
    relation = product(
        weyl12,
        first_chart_root,
        inverse(weyl12),
        inverse(second_chart_root),
    )

    transverse_positions = [
        position
        for position, (factor, matrix) in enumerate(relation)
        if factor == 2
        and not lies_in_h(aligned_matrix(
            factor, matrix, alignment, alignment_inverse
        ))
    ]
    classical_value = aligned_value(relation, alignment, alignment_inverse)
    return {
        "identity": "w_12 x_12(f) w_12^-1 x_21(f)^-1",
        "scalar_x12_word": encode_word(scalar_x12),
        "scalar_x21_word": encode_word(scalar_x21),
        "weyl_word_length": len(weyl12),
        "reduced_relation_length": len(relation),
        "transverse_second_chart_positions": transverse_positions,
        "exactly_one_transverse_second_chart_syllable": (
            len(transverse_positions) == 1
        ),
        "leavitt_relation_verified": leavitt_is_one(evaluate_word(relation)),
        "classical_alignment_relation_verified": np.array_equal(
            classical_value, I4
        ),
        "relation_word": encode_word(relation),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
