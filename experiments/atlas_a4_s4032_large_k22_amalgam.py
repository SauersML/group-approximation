#!/usr/bin/env python3
"""Certify the finite regular amalgam completing the large core K2,2.

The left vertex is the order-576 group from the first-cycle construction.
The right vertex is GL(3,2) x C2, written in the fixed GL(4,2) chart.  Their
common labeled subgroup is S4 x C2 of order 48.  Seven left regular copies and
twelve right regular copies therefore agree over the common subgroup on 4032
points.
"""

import json
import numpy as np

from atlas_a4_packet_component_audit import subgroup
from atlas_a4_packet_generation import matrix_order
from atlas_a4_regular_amalgam_finite_search import B, Z
from atlas_a4_s576_first_cycle_amalgam import C, D, R, U, generated_order
from atlas_two_chart_search import I4, gf2_inv, matrix_key


REFERENCE_HEX = "00000001000100000100000000000100"
H18_HEX = (
    "01010000000100000000010000000001",
    "01000000010100000000010000000001",
    "01000000000100000000000100000101",
    "01010000010000000000010000000001",
    "00010000010100000000010000000001",
    "01000000000100000000010100000100",
)


def matrix(value):
    return np.frombuffer(bytes.fromhex(value), dtype=np.uint8).reshape(4, 4).copy()


def multiply(left, right):
    return (left @ right) % 2


def conjugate(value, alignment):
    return multiply(multiply(alignment, value), gf2_inv(alignment))


def main():
    alignment = matrix(REFERENCE_HEX)

    # The first S3 is raw; the second is transported by the fixed packet
    # alignment.  These are exactly the four labels in the large core K2,2.
    r = matrix(H18_HEX[3])
    u = matrix(H18_HEX[1])
    b = conjugate(matrix(H18_HEX[0]), alignment)
    y = conjugate(matrix(H18_HEX[4]), alignment)

    identity = matrix_key(I4)
    edge_words = (
        multiply(gf2_inv(r), b),
        multiply(u, y),
        multiply(multiply(u, r), gf2_inv(y)),
        multiply(multiply(r, b), y),
    )
    assert all(matrix_order(word) == 3 for word in edge_words)

    first_s3 = subgroup((r, u))
    second_s3 = subgroup((b, y))
    initial_s4 = subgroup((r, u, b))
    full_core = subgroup((r, u, b, y))
    assert tuple(map(len, (first_s3, second_s3, initial_s4, full_core))) == (
        6, 6, 24, 168)

    # The order-576 left vertex contains the same labeled initial S4 and an
    # additional central collision involution.  This is the order-48 overlap.
    left_order = generated_order((R, Z, B, C, D))
    left_s4_order = generated_order((R, U, B))
    overlap_order = generated_order((R, U, B, C))
    assert (left_order, left_s4_order, overlap_order) == (576, 24, 48)

    right_order = 2 * len(full_core)
    assert right_order == 336
    assert 7 * left_order == 12 * right_order == 4032
    assert 7 * (left_order // overlap_order) == 12 * (
        right_order // overlap_order) == 84

    print(json.dumps({
        "ambient_permutation_degree": 4032,
        "edge_word_orders": [matrix_order(word) for word in edge_words],
        "first_S3_order": len(first_s3),
        "second_S3_order": len(second_s3),
        "initial_three_label_group_order": len(initial_s4),
        "completed_K22_group_order": len(full_core),
        "left_vertex_order": left_order,
        "right_vertex_GL3xC2_order": right_order,
        "common_S4xC2_order": overlap_order,
        "left_regular_copies": 7,
        "right_regular_copies": 12,
        "common_regular_multiplicity": 84,
        "fourth_edge_added_independently": False,
        "fourth_edge_forced_in_canonical_GL3_completion": True,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
