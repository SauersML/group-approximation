#!/usr/bin/env python3
"""Exact two-context soundness core for the A4 packet plus collision 19243.

The full thirty-context audit has classical conditional gap 1/5.  This script
shows that two particular packet contexts already hit every collision-perfect
inner or outer chart alignment.  All arithmetic is exact over F2.
"""

import json
import os
from collections import Counter

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_classical_gap import (
    collision_is_one,
    cube_is_one,
    decode_word,
    prepare_pair,
)
from atlas_two_chart_search import gf2_inv


CHOSEN_POSITIONS = (0, 4)
CHOSEN_TREE_INDICES = (6910, 6940)


def audit(use_outer, packet, collision):
    chosen = [packet[pos] for pos in CHOSEN_POSITIONS]
    if tuple(index for index, _ in chosen) != CHOSEN_TREE_INDICES:
        raise AssertionError(
            "packet ordering changed: expected tree indices %r, got %r"
            % (CHOSEN_TREE_INDICES, tuple(index for index, _ in chosen))
        )

    prepared = [prepare_pair(word, use_outer) for _, word in chosen]
    histogram = Counter()
    survivors = 0

    for alignment in enumerate_gl4():
        inverse = gf2_inv(alignment)
        if not collision_is_one(
            collision, alignment, inverse, None, use_outer
        ):
            continue
        survivors += 1
        bad = sum(
            not cube_is_one(pair, alignment, inverse, None)
            for pair in prepared
        )
        histogram[bad] += 1

    # The imported predicates compare against the identity key.  Pass that
    # explicit key rather than relying on an implementation detail.
    return survivors, histogram


def exact_audit(use_outer, packet, collision):
    # Keep identity construction local so this script is robust to refactors of
    # the full thirty-context audit.
    from atlas_two_chart_search import I4, matrix_key

    identity = matrix_key(I4)
    chosen = [packet[pos] for pos in CHOSEN_POSITIONS]
    if tuple(index for index, _ in chosen) != CHOSEN_TREE_INDICES:
        raise AssertionError("chosen packet indices changed")
    prepared = [prepare_pair(word, use_outer) for _, word in chosen]
    histogram = Counter()

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
        histogram[bad] += 1

    if sum(histogram.values()) != 2880:
        raise AssertionError("collision survivor count changed: %r" % histogram)
    expected = Counter({1: 1152, 2: 1728})
    if histogram != expected:
        raise AssertionError(
            "two-context soundness certificate changed: %r" % histogram
        )
    return {
        "collision_perfect_alignments": sum(histogram.values()),
        "minimum_failed_contexts": min(histogram),
        "failure_histogram": dict(sorted(histogram.items())),
    }


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as handle:
        collision = decode_word(json.load(handle)[0]["word"])

    result = {
        "chosen_packet_positions": list(CHOSEN_POSITIONS),
        "chosen_tree_indices": list(CHOSEN_TREE_INDICES),
        "inner": exact_audit(False, packet, collision),
        "outer": exact_audit(True, packet, collision),
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
