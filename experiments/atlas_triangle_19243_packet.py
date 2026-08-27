#!/usr/bin/env python3
"""Exact finite audit for the shortest A4 boundary packet plus collision 19243.

The first tensor-flip boundary in the complete radius-five atlas window contains
X-length-nine relations of the form (b_2 a_1)^3 with ord(b)=2 and ord(a)=3.
Such a relation is the (2,3,3) triangle relation, hence an A4 relation.

This script extracts every such shortest pair-cube from the exact radius-five
kernel enumeration, then exhausts all 40,320 classical automorphism alignments
of the two regular A8 charts.  It checks how many alignments satisfy the whole
triangle packet, and how many also satisfy the established interior collision
19243.  All group arithmetic is exact over F2.
"""

import json
import os

import numpy as np

from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import I4, factor_generators, gf2_inv, gf2_mul, matrix_key


def outer(matrix):
    return gf2_inv(matrix).T.copy()


def matrix_order(matrix):
    value = I4.copy()
    for exponent in range(1, 16):
        value = gf2_mul(value, matrix)
        if matrix_key(value) == matrix_key(I4):
            return exponent
    raise AssertionError("element order exceeds GL(4,2) bound")


def x_lengths():
    """Exact word metric from the six adjacent-transvection generators."""
    generators = [word[0][1] for _, word in factor_generators()[:6]]
    lengths = {matrix_key(I4): 0}
    frontier = [I4.copy()]
    while frontier:
        nxt = []
        for element in frontier:
            depth = lengths[matrix_key(element)]
            for generator in generators:
                target = gf2_mul(element, generator)
                key = matrix_key(target)
                if key not in lengths:
                    lengths[key] = depth + 1
                    nxt.append(target)
        frontier = nxt
    if len(lengths) != 20160:
        raise AssertionError("word metric did not enumerate GL(4,2)")
    return lengths


def is_pair_cube(word):
    if len(word) != 6:
        return False
    factors = [factor for factor, _ in word]
    if factors not in ([1, 2, 1, 2, 1, 2], [2, 1, 2, 1, 2, 1]):
        return False
    first = word[0][1]
    second = word[1][1]
    return all(matrix_key(word[i][1]) == matrix_key(first) for i in (0, 2, 4)) and all(
        matrix_key(word[i][1]) == matrix_key(second) for i in (1, 3, 5)
    )


def select_triangle_packet(words, lengths):
    selected = []
    for index, word in enumerate(words):
        if not is_pair_cube(word):
            continue
        xlen = sum(lengths[matrix_key(matrix)] for _, matrix in word)
        if xlen != 9:
            continue
        orders = {matrix_order(word[0][1]), matrix_order(word[1][1])}
        if orders != {2, 3}:
            continue
        selected.append((index, word))
    if len(selected) != 30:
        raise AssertionError(f"expected 30 shortest A4 pair-cubes, found {len(selected)}")
    return selected


def aligned_value(word, alignment, alignment_inverse, use_outer=False):
    value = I4.copy()
    for factor, matrix in word:
        image = matrix
        if factor == 2:
            if use_outer:
                image = outer(image)
            image = gf2_mul(gf2_mul(alignment, image), alignment_inverse)
        value = gf2_mul(value, image)
    return matrix_key(value)


def decode_word(payload):
    word = []
    for syllable in payload:
        matrix = np.frombuffer(
            bytes.fromhex(syllable["matrix_f2_hex"]), dtype=np.uint8
        ).reshape(4, 4).copy()
        word.append((int(syllable["factor"]), matrix))
    return word


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    lengths = x_lengths()
    packet = select_triangle_packet(words, lengths)

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as handle:
        collision = decode_word(json.load(handle)[0]["word"])

    identity = matrix_key(I4)
    elements = enumerate_gl4()
    counts = {}
    survivors = {}
    for use_outer in (False, True):
        triangle_survivors = []
        combined_survivors = []
        for alignment in elements:
            inverse = gf2_inv(alignment)
            if all(
                aligned_value(word, alignment, inverse, use_outer) == identity
                for _, word in packet
            ):
                triangle_survivors.append(matrix_key(alignment).hex())
                if aligned_value(collision, alignment, inverse, use_outer) == identity:
                    combined_survivors.append(matrix_key(alignment).hex())
        label = "outer" if use_outer else "inner"
        counts[label] = {
            "triangle_packet_survivors": len(triangle_survivors),
            "triangle_plus_19243_survivors": len(combined_survivors),
        }
        survivors[label] = triangle_survivors

    expected = {
        "triangle_packet_survivors": 30,
        "triangle_plus_19243_survivors": 0,
    }
    if counts["inner"] != expected:
        raise AssertionError(f"inner calibration changed: {counts['inner']}")
    if counts["outer"] != expected:
        raise AssertionError(f"outer calibration changed: {counts['outer']}")

    example_index, example = packet[0]
    result = {
        "radius_five_tree_generators": len(words),
        "shortest_a4_pair_cubes": len(packet),
        "pair_cube_tree_indices": [index for index, _ in packet],
        "example": {
            "tree_index": example_index,
            "free_product_syllable_length": len(example),
            "x_length": sum(lengths[matrix_key(matrix)] for _, matrix in example),
            "syllable_orders": [matrix_order(example[0][1]), matrix_order(example[1][1])],
            "word": [
                {"factor": factor, "matrix_f2_hex": matrix_key(matrix).hex()}
                for factor, matrix in example
            ],
        },
        "automorphism_alignments_tested_per_coset": len(elements),
        "counts": counts,
        "triangle_survivor_alignment_hex": survivors,
    }
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
