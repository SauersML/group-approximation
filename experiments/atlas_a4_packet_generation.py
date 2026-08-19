#!/usr/bin/env python3
"""Exact generation audit for the thirty shortest A4 atlas contexts.

The packet is already certified by atlas_triangle_19243_packet.py.  This script
asks a different finite question: do the chart letters which actually occur in
those thirty contexts generate the whole A8 chart on each side?

All group arithmetic is exact over F2.  The expected answer is 20160 on both
factors.
"""

import json

from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_two_chart_search import I4, factor_generators, gf2_mul, matrix_key


def matrix_order(matrix):
    value = I4.copy()
    for exponent in range(1, 16):
        value = gf2_mul(value, matrix)
        if matrix_key(value) == matrix_key(I4):
            return exponent
    raise AssertionError("element order exceeds GL(4,2) bound")


def x_lengths():
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
    return (
        all(matrix_key(word[i][1]) == matrix_key(first) for i in (0, 2, 4))
        and all(matrix_key(word[i][1]) == matrix_key(second) for i in (1, 3, 5))
    )


def select_packet(words, lengths):
    packet = []
    for index, word in enumerate(words):
        if not is_pair_cube(word):
            continue
        if sum(lengths[matrix_key(matrix)] for _, matrix in word) != 9:
            continue
        if {matrix_order(word[0][1]), matrix_order(word[1][1])} != {2, 3}:
            continue
        packet.append((index, word))
    if len(packet) != 30:
        raise AssertionError(f"expected 30 shortest A4 contexts, got {len(packet)}")
    return packet


def subgroup_size(generators):
    seen = {matrix_key(I4)}
    frontier = [I4.copy()]
    while frontier:
        nxt = []
        for element in frontier:
            for generator in generators:
                target = gf2_mul(element, generator)
                key = matrix_key(target)
                if key not in seen:
                    seen.add(key)
                    nxt.append(target)
        frontier = nxt
    return len(seen)


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    output = {"packet_size": len(packet), "factors": {}}
    for factor in (1, 2):
        generators = {}
        for _, word in packet:
            # A pair cube repeats its two letters three times; scanning the
            # whole word is robust to the factor-reversed orientation.
            for f, matrix in word:
                if f == factor:
                    generators[matrix_key(matrix)] = matrix
        size = subgroup_size(list(generators.values()))
        if size != 20160:
            raise AssertionError(f"factor {factor} generated subgroup of size {size}")
        output["factors"][str(factor)] = {
            "distinct_packet_letters": len(generators),
            "orders": sorted({matrix_order(m) for m in generators.values()}),
            "generated_subgroup_size": size,
        }

    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
