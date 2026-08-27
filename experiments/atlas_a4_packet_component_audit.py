#!/usr/bin/env python3
"""Exact subgroup-component audit for the thirty shortest A4 packet words.

The packet looks like thirty unrelated mixed relations, but its ten chart
letters split into two disconnected bipartite constraint components.  This
script recovers those components and identifies the subgroups they generate.
All arithmetic is exact over F2.
"""

import json
from collections import defaultdict

from atlas_a4_packet_generation import matrix_order, select_packet, x_lengths
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_two_chart_search import I4, gf2_mul, matrix_key


BRIDGE_ENDPOINTS = {
    "h": "01000000000101000001000000000001",
    "k": "01010000010000000000010000000001",
    "z": "01000000000100000000010100000100",
    "b": "01000000000100000000010100000001",
}


def subgroup(generators):
    seen = {matrix_key(I4): I4.copy()}
    todo = [I4.copy()]
    while todo:
        value = todo.pop()
        for generator in generators:
            target = gf2_mul(value, generator)
            key = matrix_key(target)
            if key not in seen:
                seen[key] = target
                todo.append(target)
    return seen


def center(group):
    return [
        a
        for a in group.values()
        if all(
            matrix_key(gf2_mul(a, b)) == matrix_key(gf2_mul(b, a))
            for b in group.values()
        )
    ]


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    matrices = {}
    edges = []
    graph = defaultdict(set)
    for index, word in packet:
        by_factor = {}
        for factor, matrix in word:
            by_factor[factor] = matrix
        order_two_factor = next(
            factor for factor, matrix in by_factor.items() if matrix_order(matrix) == 2
        )
        order_three_factor = 3 - order_two_factor
        b = by_factor[order_two_factor]
        a = by_factor[order_three_factor]
        bk, ak = matrix_key(b), matrix_key(a)
        matrices[bk], matrices[ak] = b, a
        edges.append((index, order_two_factor, bk, ak))
        graph[bk].add(ak)
        graph[ak].add(bk)

    remaining = set(graph)
    components = []
    while remaining:
        start = min(remaining)
        component = {start}
        todo = [start]
        while todo:
            vertex = todo.pop()
            for neighbour in graph[vertex]:
                if neighbour not in component:
                    component.add(neighbour)
                    todo.append(neighbour)
        components.append(component)
        remaining -= component
    components.sort(key=lambda component: (len(component), sorted(component)))

    records = []
    generated = []
    for component in components:
        involutions = sorted(
            key for key in component if matrix_order(matrices[key]) == 2
        )
        order_threes = sorted(
            key for key in component if matrix_order(matrices[key]) == 3
        )
        group = subgroup([matrices[key] for key in component])
        generated.append(group)
        involution_group = subgroup([matrices[key] for key in involutions])
        component_edges = [edge for edge in edges if edge[2] in component]
        record = {
            "letter_count": len(component),
            "involutions": len(involutions),
            "order_three_letters": len(order_threes),
            "packet_words": len(component_edges),
            "unique_unoriented_pairs": len({(b, a) for _, _, b, a in component_edges}),
            "unique_oriented_pairs": len(
                {(factor, b, a) for _, factor, b, a in component_edges}
            ),
            "generated_subgroup_size": len(group),
            "center_size": len(center(group)),
            "involution_generated_subgroup_size": len(involution_group),
            "tree_indices": [index for index, _, _, _ in component_edges],
            "involution_labels_hex": [key.hex() for key in involutions],
            "order_three_labels_hex": [key.hex() for key in order_threes],
            "ordered_pair_occurrences": [
                {
                    "tree_index": index,
                    "order_two_chart_factor": factor,
                    "involution_hex": b.hex(),
                    "order_three_hex": a.hex(),
                }
                for index, factor, b, a in component_edges
            ],
            # With b_0--a_0, b_0--a_j and b_1--a_0 as the spanning tree,
            # the remaining edge b_1--a_j carries this canonical rectangle.
            # These records freeze the exact labels needed by a subsequent
            # qutrit/multiplicity-wire compiler; no matrix variable is chosen
            # at this finite-group audit stage.
            "canonical_fundamental_rectangles": [
                {
                    "b0_hex": involutions[0].hex(),
                    "b1_hex": involutions[1].hex(),
                    "a0_hex": order_threes[0].hex(),
                    "aj_hex": order_threes[j].hex(),
                    "holonomy_word": "M(b1,aj) M(b0,aj)^* M(b0,a0) M(b1,a0)^*",
                }
                for j in range(1, len(order_threes))
            ],
        }
        records.append(record)

    signatures = [
        (
            record["involutions"],
            record["order_three_letters"],
            record["packet_words"],
            record["unique_unoriented_pairs"],
            record["generated_subgroup_size"],
            record["center_size"],
            record["involution_generated_subgroup_size"],
        )
        for record in records
    ]
    expected = [
        (2, 2, 7, 4, 6, 1, 6),
        (2, 4, 23, 8, 18, 3, 6),
    ]
    if signatures != expected:
        raise AssertionError(f"packet component structure changed: {signatures!r}")

    intersection_size = len(set(generated[0]) & set(generated[1]))
    if intersection_size != 1:
        raise AssertionError(f"component subgroup intersection changed: {intersection_size}")
    joined = subgroup([matrices[key] for key in set().union(*components)])
    if len(joined) != 20160:
        raise AssertionError(f"component subgroups no longer generate A8: {len(joined)}")

    component_hex = [
        {key.hex() for key in component}
        for component in components
    ]
    endpoint_localization = {}
    for name, hex_value in BRIDGE_ENDPOINTS.items():
        memberships = [
            index for index, labels in enumerate(component_hex)
            if hex_value in labels
        ]
        endpoint_localization[name] = {
            "matrix_f2_hex": hex_value,
            "packet_component": memberships[0] if memberships else None,
        }
    expected_localization = {
        "h": 0,
        "k": 1,
        "z": 1,
        "b": None,
    }
    if {
        name: record["packet_component"]
        for name, record in endpoint_localization.items()
    } != expected_localization:
        raise AssertionError(f"bridge endpoint localization changed: {endpoint_localization}")

    output = {
        "packet_size": len(packet),
        "distinct_letters": len(matrices),
        "unique_unoriented_pair_constraints": len({(b, a) for _, _, b, a in edges}),
        "unique_oriented_pair_constraints": len(
            {(factor, b, a) for _, factor, b, a in edges}
        ),
        "component_subgroup_intersection_size": intersection_size,
        "joined_component_subgroup_size": len(joined),
        "two_holonomy_bridge_endpoint_localization": endpoint_localization,
        "two_holonomy_bridge_structure": {
            "c": "h*k joins the order-three vertices of components 0 and 1",
            "a": "z*b joins the central-C3 packet vertex z to the collision-only involution b",
        },
        "components": records,
    }
    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
