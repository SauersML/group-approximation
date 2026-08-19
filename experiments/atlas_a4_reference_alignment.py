#!/usr/bin/env python3
"""Freeze one exact inner alignment for the thirty shortest A4 packet.

The shifted-centralizer compiler needs a *reference* relative chart alignment:
the two chart alphabets cannot be identified naively, because several packet
order-two/order-three pairs do not generate A4 in one chart.  This script
replays the exact radius-five packet extraction, enumerates the 20,160 inner
A8 alignments, and freezes the lexicographically first alignment satisfying all
thirty pair-cubes.

All arithmetic is exact over F2.
"""

from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import aligned_value, select_triangle_packet, x_lengths
from atlas_two_chart_search import I4, matrix_key


EXPECTED_HEX = "00000001000100000100000000000100"


def matrix_order(matrix):
    from atlas_two_chart_search import gf2_mul

    value = I4.copy()
    for exponent in range(1, 16):
        value = gf2_mul(value, matrix)
        if matrix_key(value) == matrix_key(I4):
            return exponent
    raise AssertionError("element order exceeds GL(4,2) bound")


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_triangle_packet(words, x_lengths())
    identity = matrix_key(I4)

    survivors = []
    for alignment in enumerate_gl4():
        inverse = __import__("atlas_two_chart_search").gf2_inv(alignment)
        if all(
            aligned_value(word, alignment, inverse, False) == identity
            for _, word in packet
        ):
            survivors.append(alignment)

    assert len(survivors) == 30
    reference = min(survivors, key=lambda matrix: matrix_key(matrix).hex())
    assert matrix_key(reference).hex() == EXPECTED_HEX
    assert matrix_order(reference) == 3

    print("inner packet alignments: 30")
    print("reference alignment hex:", EXPECTED_HEX)
    print("reference alignment order: 3")


if __name__ == "__main__":
    main()
