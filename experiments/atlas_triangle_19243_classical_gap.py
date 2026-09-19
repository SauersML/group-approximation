#!/usr/bin/env python3
"""Exact classical soundness gap for the A4 packet plus collision 19243.

Among chart automorphism alignments that satisfy collision 19243 exactly, count
how many of the thirty shortest A4 pair-cubes must fail.  The answer is six for
both the inner and outer automorphism cosets: a 1/5 constraint gap.

All arithmetic is exact over F2.  The script is a strengthening of
atlas_triangle_19243_packet.py: that script only checks that zero triangle
violations and zero collision violations cannot occur simultaneously.
"""

import json
import os
from collections import Counter

import numpy as np

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


def outer(matrix):
    return gf2_inv(matrix).T.copy()


def decode_word(payload):
    out = []
    for syllable in payload:
        matrix = np.frombuffer(
            bytes.fromhex(syllable["matrix_f2_hex"]), dtype=np.uint8
        ).reshape(4, 4).copy()
        out.append((int(syllable["factor"]), matrix))
    return out


def conjugate(alignment, inverse, matrix):
    return gf2_mul(gf2_mul(alignment, matrix), inverse)


def prepare_pair(packet_word, use_outer):
    first_factor, first = packet_word[0]
    second_factor, second = packet_word[1]
    if use_outer and first_factor == 2:
        first = outer(first)
    if use_outer and second_factor == 2:
        second = outer(second)
    return first_factor, first, second_factor, second


def cube_is_one(pair, alignment, inverse, identity):
    f1, m1, f2, m2 = pair
    x1 = conjugate(alignment, inverse, m1) if f1 == 2 else m1
    x2 = conjugate(alignment, inverse, m2) if f2 == 2 else m2
    product = gf2_mul(x1, x2)
    cube = gf2_mul(gf2_mul(product, product), product)
    return matrix_key(cube) == identity


def collision_is_one(collision, alignment, inverse, identity, use_outer):
    value = I4.copy()
    for factor, matrix in collision:
        image = outer(matrix) if use_outer and factor == 2 else matrix
        if factor == 2:
            image = conjugate(alignment, inverse, image)
        value = gf2_mul(value, image)
    return matrix_key(value) == identity


def audit(use_outer, packet, collision):
    identity = matrix_key(I4)
    prepared = [prepare_pair(word, use_outer) for _, word in packet]
    conditioned = Counter()
    examples = []
    best = len(prepared) + 1

    for alignment in enumerate_gl4():
        inverse = gf2_inv(alignment)
        if not collision_is_one(
            collision, alignment, inverse, identity, use_outer
        ):
            continue
        bad = sum(
            not cube_is_one(pair, alignment, inverse, identity)
            for pair in prepared
        )
        conditioned[bad] += 1
        if bad < best:
            best = bad
            examples = [matrix_key(alignment).hex()]
        elif bad == best and len(examples) < 4:
            examples.append(matrix_key(alignment).hex())

    if sum(conditioned.values()) != 2880:
        raise AssertionError(f"collision survivor count changed: {conditioned}")
    if best != 6 or conditioned[6] != 4:
        raise AssertionError(f"classical gap changed: {conditioned}")

    return {
        "collision_perfect_alignments": sum(conditioned.values()),
        "minimum_failed_triangle_contexts": best,
        "minimum_failed_fraction": [best, len(prepared)],
        "minimizer_count": conditioned[best],
        "example_minimizers": examples,
        "conditioned_failure_histogram": dict(sorted(conditioned.items())),
    }


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as handle:
        collision = decode_word(json.load(handle)[0]["word"])

    result = {
        "triangle_contexts": len(packet),
        "inner": audit(False, packet, collision),
        "outer": audit(True, packet, collision),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
