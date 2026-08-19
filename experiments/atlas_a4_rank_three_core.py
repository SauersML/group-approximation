#!/usr/bin/env python3
"""Exact audit of the 14-word rank-three core inside the A4 packet.

The large packet component is S3 x C3.  Remove the pair-cubes whose order-three
letter lies in the nontrivial central C3.  What remains is two K2,2 gadgets
whose two S3 subgroups generate the standard GL3(2) inside GL4(2).

The script also checks the full classical alignment sector: the 14-word core
has exactly the same inner/outer survivors as all 30 packet words, and collision
19243 kills every one of them.
"""

import json
import os
from collections import defaultdict

import numpy as np

from atlas_a4_packet_component_audit import center, subgroup
from atlas_a4_packet_generation import matrix_order, select_packet, x_lengths
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import aligned_value, decode_word
from atlas_two_chart_search import I4, gf2_inv, matrix_key


H18_LABEL_HEX = (
    "01010000000100000000010000000001",
    "01000000010100000000010000000001",
    "01000000000100000000000100000101",
    "01010000010000000000010000000001",
    "00010000010100000000010000000001",
    "01000000000100000000010100000100",
)


def matrix(hex_value):
    return np.frombuffer(bytes.fromhex(hex_value), dtype=np.uint8).reshape(4, 4).copy()


def rank_three(matrix_value):
    return (
        tuple(int(x) for x in matrix_value[3, :]) == (0, 0, 0, 1)
        and tuple(int(x) for x in matrix_value[:, 3]) == (0, 0, 0, 1)
    )


def packet_edge(word):
    by_factor = {factor: value for factor, value in word}
    b = next(value for value in by_factor.values() if matrix_order(value) == 2)
    a = next(value for value in by_factor.values() if matrix_order(value) == 3)
    b_factor = next(factor for factor, value in by_factor.items() if matrix_order(value) == 2)
    return b_factor, b, a


def components(edges):
    graph = defaultdict(set)
    matrices = {}
    for _index, _factor, b, a in edges:
        bk, ak = matrix_key(b), matrix_key(a)
        matrices[bk], matrices[ak] = b, a
        graph[bk].add(ak)
        graph[ak].add(bk)
    remaining = set(graph)
    out = []
    while remaining:
        start = min(remaining)
        component = {start}
        todo = [start]
        while todo:
            old = todo.pop()
            for new in graph[old]:
                if new not in component:
                    component.add(new)
                    todo.append(new)
        out.append(component)
        remaining -= component
    out.sort(key=lambda c: sorted(c))
    return out, matrices


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    h18 = subgroup([matrix(value) for value in H18_LABEL_HEX])
    central_order_three = {
        matrix_key(value) for value in center(h18)
        if matrix_key(value) != matrix_key(I4)
    }
    assert len(central_order_three) == 2

    core = []
    transverse = []
    for index, word in packet:
        factor, b, a = packet_edge(word)
        entry = (index, factor, b, a)
        if matrix_key(a) in central_order_three:
            transverse.append(entry)
        else:
            core.append(entry)

    assert len(core) == 14
    assert len(transverse) == 16
    assert len({(matrix_key(b), matrix_key(a)) for _, _, b, a in core}) == 8
    assert len({(factor, matrix_key(b), matrix_key(a)) for _, factor, b, a in core}) == 8

    comps, matrices = components(core)
    assert len(comps) == 2
    generated = []
    component_records = []
    for comp in comps:
        comp_edges = [entry for entry in core if matrix_key(entry[2]) in comp]
        involutions = [key for key in comp if matrix_order(matrices[key]) == 2]
        order_threes = [key for key in comp if matrix_order(matrices[key]) == 3]
        group = subgroup([matrices[key] for key in comp])
        generated.append(group)
        assert (len(involutions), len(order_threes)) == (2, 2)
        assert len(comp_edges) == 7
        assert len({(matrix_key(b), matrix_key(a)) for _, _, b, a in comp_edges}) == 4
        assert len(group) == 6
        component_records.append({
            "packet_words": len(comp_edges),
            "distinct_pairs": 4,
            "generated_subgroup_order": 6,
            "tree_indices": [index for index, _, _, _ in comp_edges],
        })

    rank_three_group = subgroup(list(generated[0].values()) + list(generated[1].values()))
    assert len(rank_three_group) == 168
    assert all(rank_three(value) for value in rank_three_group.values())

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as handle:
        collision = decode_word(json.load(handle)[0]["word"])

    identity = matrix_key(I4)
    elements = enumerate_gl4()
    alignment_counts = {}
    for use_outer in (False, True):
        core_survivors = []
        full_survivors = []
        core_plus_collision = []
        full_plus_collision = []
        for alignment in elements:
            inverse = gf2_inv(alignment)
            core_ok = all(
                aligned_value(words[index], alignment, inverse, use_outer) == identity
                for index, _, _, _ in core
            )
            if not core_ok:
                continue
            alignment_hex = matrix_key(alignment).hex()
            core_survivors.append(alignment_hex)
            full_ok = all(
                aligned_value(word, alignment, inverse, use_outer) == identity
                for _, word in packet
            )
            if full_ok:
                full_survivors.append(alignment_hex)
            collision_ok = aligned_value(collision, alignment, inverse, use_outer) == identity
            if collision_ok:
                core_plus_collision.append(alignment_hex)
                if full_ok:
                    full_plus_collision.append(alignment_hex)

        assert core_survivors == full_survivors
        assert len(core_survivors) == 30
        assert not core_plus_collision
        assert not full_plus_collision
        alignment_counts["outer" if use_outer else "inner"] = {
            "core_survivors": 30,
            "full_packet_survivors": 30,
            "core_plus_19243_survivors": 0,
            "full_packet_plus_19243_survivors": 0,
        }

    print(json.dumps({
        "core_packet_words": len(core),
        "discarded_central_C3_words": len(transverse),
        "core_components": component_records,
        "joined_core_subgroup_order": len(rank_three_group),
        "joined_core_is_standard_GL3": True,
        "alignment_counts": alignment_counts,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
