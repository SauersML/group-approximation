#!/usr/bin/env python3
"""Freeze one exact inner alignment for the thirty shortest A4 packet.

The shifted-centralizer compiler needs a *reference* relative chart alignment:
the two chart alphabets cannot be identified naively, because several packet
order-two/order-three pairs do not generate A4 in one chart.  This script
replays the exact radius-five packet extraction, enumerates the 20,160 inner
A8 alignments, and freezes the lexicographically first alignment satisfying all
thirty pair-cubes.

It also computes the subgroup geometry of the two connected components of the
packet pair graph after applying that reference alignment.  The four-label
component generates S3; its aligned conjugate is disjoint and together they
generate the rank-three GL3(F2) core.  The six-label component generates
S3 x C3; its aligned conjugate is disjoint and together they generate all A8.

All arithmetic is exact over F2.
"""

from collections import deque

from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import aligned_value, select_triangle_packet, x_lengths
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


EXPECTED_HEX = "00000001000100000100000000000100"


def matrix_order(matrix):
    value = I4.copy()
    for exponent in range(1, 16):
        value = gf2_mul(value, matrix)
        if matrix_key(value) == matrix_key(I4):
            return exponent
    raise AssertionError("element order exceeds GL(4,2) bound")


def generated_subgroup(generators):
    generators = list(generators)
    moves = generators + [gf2_inv(generator) for generator in generators]
    seen = {matrix_key(I4): I4.copy()}
    queue = deque([I4.copy()])
    while queue:
        value = queue.popleft()
        for generator in moves:
            target = gf2_mul(value, generator)
            key = matrix_key(target)
            if key not in seen:
                seen[key] = target
                queue.append(target)
    return list(seen.values())


def pair_graph_components(packet):
    labels = {}
    adjacency = {}
    for _index, word in packet:
        by_factor = {}
        for factor, matrix in word:
            by_factor.setdefault(factor, matrix)
        if set(by_factor) != {1, 2}:
            raise AssertionError("pair cube stopped using both atlas factors")
        left = matrix_key(by_factor[1])
        right = matrix_key(by_factor[2])
        labels[left] = by_factor[1]
        labels[right] = by_factor[2]
        adjacency.setdefault(left, set()).add(right)
        adjacency.setdefault(right, set()).add(left)

    components = []
    unseen = set(adjacency)
    while unseen:
        start = unseen.pop()
        component = {start}
        queue = deque([start])
        while queue:
            vertex = queue.popleft()
            for target in adjacency[vertex]:
                if target not in component:
                    component.add(target)
                    unseen.discard(target)
                    queue.append(target)
        components.append([labels[key] for key in component])
    return sorted(components, key=len)


def component_geometry(component, reference):
    reference_inverse = gf2_inv(reference)
    raw = generated_subgroup(component)
    aligned_generators = [
        gf2_mul(gf2_mul(reference, value), reference_inverse)
        for value in component
    ]
    aligned = generated_subgroup(aligned_generators)
    joined = generated_subgroup(component + aligned_generators)
    raw_keys = {matrix_key(value) for value in raw}
    aligned_keys = {matrix_key(value) for value in aligned}
    return {
        "labels": len(component),
        "raw_subgroup_order": len(raw),
        "aligned_subgroup_order": len(aligned),
        "intersection_order": len(raw_keys & aligned_keys),
        "join_order": len(joined),
    }


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_triangle_packet(words, x_lengths())
    identity = matrix_key(I4)

    survivors = []
    for alignment in enumerate_gl4():
        inverse = gf2_inv(alignment)
        if all(
            aligned_value(word, alignment, inverse, False) == identity
            for _, word in packet
        ):
            survivors.append(alignment)

    assert len(survivors) == 30
    reference = min(survivors, key=lambda matrix: matrix_key(matrix).hex())
    assert matrix_key(reference).hex() == EXPECTED_HEX
    assert matrix_order(reference) == 3

    geometry = [
        component_geometry(component, reference)
        for component in pair_graph_components(packet)
    ]
    expected = [
        {
            "labels": 4,
            "raw_subgroup_order": 6,
            "aligned_subgroup_order": 6,
            "intersection_order": 1,
            "join_order": 168,
        },
        {
            "labels": 6,
            "raw_subgroup_order": 18,
            "aligned_subgroup_order": 18,
            "intersection_order": 1,
            "join_order": 20160,
        },
    ]
    if geometry != expected:
        raise AssertionError(geometry)

    print("inner packet alignments: 30")
    print("reference alignment hex:", EXPECTED_HEX)
    print("reference alignment order: 3")
    print("aligned component geometry:", geometry)


if __name__ == "__main__":
    main()
