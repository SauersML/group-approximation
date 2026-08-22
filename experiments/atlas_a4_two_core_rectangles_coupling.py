#!/usr/bin/env python3
"""Exact GL(4,2) audit of the second core K2,2 and rectangle coupling."""

import json
import numpy as np

from atlas_a4_packet_component_audit import subgroup
from atlas_a4_packet_generation import matrix_order
from atlas_two_chart_search import gf2_inv, matrix_key


REFERENCE_HEX = "00000001000100000100000000000100"
H18_HEX = (
    "01010000000100000000010000000001",
    "01000000010100000000010000000001",
    "01000000000100000000000100000101",
    "01010000010000000000010000000001",
    "00010000010100000000010000000001",
    "01000000000100000000010100000100",
)
H6_HEX = (
    "01000000000101000000010000000001",  # h0, involution
    "01000000000100000001010000000001",  # h1, involution
    "01000000000101000001000000000001",  # a
    "01000000000001000001010000000001",  # a^-1
)
COLLISION_HEX = "01000000000100000000010100000001"


def matrix(value):
    return np.frombuffer(bytes.fromhex(value), dtype=np.uint8).reshape(4, 4).copy()


def multiply(left, right):
    return (left @ right) % 2


def main():
    alignment = matrix(REFERENCE_HEX)
    alignment_inverse = gf2_inv(alignment)

    def aligned(value):
        return multiply(multiply(alignment, value), alignment_inverse)

    h0, h1, a, a_inverse = map(matrix, H6_HEX)
    small_edges = (
        multiply(a_inverse, aligned(h0)),
        multiply(h0, aligned(a_inverse)),
        multiply(h1, aligned(a)),
        multiply(a, aligned(h1)),
    )
    assert all(matrix_order(word) == 3 for word in small_edges)

    small_generators = (h0, h1, a, a_inverse,
                        aligned(h0), aligned(h1), aligned(a), aligned(a_inverse))
    second_rectangle = subgroup(small_generators)
    assert len(second_rectangle) == 168

    first_generators = (
        matrix(H18_HEX[3]),
        matrix(H18_HEX[1]),
        aligned(matrix(H18_HEX[0])),
        aligned(matrix(H18_HEX[4])),
    )
    first_rectangle = subgroup(first_generators)
    coupled = subgroup(first_generators + small_generators)
    intersection = set(first_rectangle) & set(second_rectangle)
    assert (len(first_rectangle), len(intersection), len(coupled)) == (168, 6, 20160)

    # The collision coefficient is not an independent central C2 after the
    # rectangles are coupled: it lies in the second GL3.  It does centralize
    # the initial S4 overlap, but the 19243 collision word evaluates back to
    # this nontrivial involution in the canonical A8 coupling.
    collision = matrix(COLLISION_HEX)
    assert matrix_key(collision) in second_rectangle
    r, u, b, y = first_generators
    assert all(
        matrix_key(multiply(collision, value)) == matrix_key(multiply(value, collision))
        for value in (r, u, b)
    )
    overlap = subgroup((r, u, b, collision))
    assert len(overlap) == 48
    t = gf2_inv(y)
    s = multiply(b, y)
    collision_word = multiply(
        multiply(
            multiply(
                multiply(
                    multiply(
                        multiply(
                            multiply(
                                multiply(t, collision), s), collision),
                        gf2_inv(t)), collision), s), t), collision)
    assert matrix_key(collision_word) == matrix_key(collision)
    assert matrix_order(collision_word) == 2
    canonical_collision_packet = subgroup((b, y, collision))
    assert len(canonical_collision_packet) == 24
    assert matrix_order(multiply(y, collision)) == 3
    assert matrix_order(multiply(multiply(b, y), collision)) == 4

    print(json.dumps({
        "second_rectangle_edge_word_orders": [matrix_order(word) for word in small_edges],
        "first_rectangle_GL3_order": len(first_rectangle),
        "second_rectangle_GL3_order": len(second_rectangle),
        "rectangle_intersection_S3_order": len(intersection),
        "coupled_chart_A8_order": len(coupled),
        "canonical_coupling_index_over_each_GL3": len(coupled) // len(first_rectangle),
        "collision_lies_in_second_rectangle": True,
        "initial_overlap_S4xC2_order": len(overlap),
        "collision_word_order_in_canonical_coupling": matrix_order(collision_word),
        "collision_word_equals_collision_involution": True,
        "canonical_b_y_c_packet_order": len(canonical_collision_packet),
        "canonical_y_c_order": matrix_order(multiply(y, collision)),
        "canonical_b_y_c_product_order": matrix_order(multiply(multiply(b, y), collision)),
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
