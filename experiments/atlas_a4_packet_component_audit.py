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
        involutions = [key for key in component if matrix_order(matrices[key]) == 2]
        order_threes = [key for key in component if matrix_order(matrices[key]) == 3]
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

    output = {
        "packet_size": len(packet),
        "distinct_letters": len(matrices),
        "unique_unoriented_pair_constraints": len({(b, a) for _, _, b, a in edges}),
        "unique_oriented_pair_constraints": len(
            {(factor, b, a) for _, factor, b, a in edges}
        ),
        "component_subgroup_intersection_size": intersection_size,
        "joined_component_subgroup_size": len(joined),
        "components": records,
    }
    print(json.dumps(output, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
