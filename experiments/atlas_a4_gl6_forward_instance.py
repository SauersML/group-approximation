#!/usr/bin/env python3
"""Emit the exact 6-dimensional Boolean instance for one forward C3 edge."""

import json

from atlas_a4_gl5_core_collision_countermodel import CENTRAL_C3_HEX
from atlas_a4_gl6_bordered_forward_search import forward_representative
from atlas_a4_parabolic_completion import core_and_collision
from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_t30_parabolic_c3_bridge import H6_LABELS, Q_SECOND


def encode_word(word):
    return [
        [factor, [[int(bit) for bit in row] for row in matrix]]
        for factor, matrix in word
    ]


def main():
    core, collision = core_and_collision()
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = [word for _index, word in select_packet(words, x_lengths())]
    forward, first_hex, second_hex = forward_representative(packet)
    print(json.dumps({
        "central_c3_hex": sorted(CENTRAL_C3_HEX),
        "collision": encode_word(collision),
        "core": [encode_word(word) for word in core],
        "forward": encode_word(forward),
        "forward_first_hex": first_hex,
        "forward_second_hex": second_hex,
        "rank_three_generators": [
            [[int(bit) for bit in row] for row in matrix]
            for matrix in tuple(H6_LABELS) + tuple(Q_SECOND)
        ],
    }, separators=(",", ":")))


if __name__ == "__main__":
    main()
