"""Test whether a hard atlas prefix pair contains two child isometries.

For every one of the six distinct hard pairs ``(q,l)``, the existing
certificate recovers the six cylinders in ``BASE_CODE`` and uses one corner
of ``l`` to identify a base cylinder with one of its proper children.  This
script exhausts all one-letter corners of ``l`` and ``l*`` and records every
base-to-child equivalence whose base endpoints lie in one support component
of ``q``.  Two complementary children of the same base cylinder would give
an immediate Cuntz--Leavitt trace obstruction.
"""

import argparse
import json
import sys

sys.path.insert(0, "experiments")

from atlas_survivor_infinite_projection import (  # noqa: E402
    BASE_CODE,
    hard_pairs,
    support_graph,
)
from atlas_survivor_prefix_gallery import chart_matrix  # noqa: E402
from atlas_survivor_prefix_obstruction import leavitt_star  # noqa: E402
from atlas_survivor_infinite_projection import corner  # noqa: E402
from atlas_kernel_collision_enumerator import ONE  # noqa: E402
from atlas_two_chart_search import leavitt_mul  # noqa: E402


def components(matrix):
    graph = support_graph(matrix)
    result = []
    unseen = set(range(len(BASE_CODE)))
    while unseen:
        root = min(unseen)
        component = {root}
        queue = [root]
        while queue:
            vertex = queue.pop()
            for following in graph[vertex]:
                if following not in component:
                    component.add(following)
                    queue.append(following)
        result.append(component)
        unseen -= component
    return result


def single_monomial(value):
    if len(value) != 1:
        return None
    (left, right), coefficient = next(iter(value.items()))
    if coefficient != 1:
        return None
    return "".join(map(str, left)), "".join(map(str, right))


def child_edges(q, letter):
    matrix = chart_matrix(q, BASE_CODE)
    component_of = {
        vertex: component_index
        for component_index, component in enumerate(components(matrix))
        for vertex in component
    }
    edges = []
    for letter_name, value in (("l", letter), ("l*", leavitt_star(letter))):
        for range_index, range_leaf in enumerate(BASE_CODE):
            for source_index, source_leaf in enumerate(BASE_CODE):
                monomial = single_monomial(corner(range_leaf, value, source_leaf))
                if monomial is None:
                    continue
                left, right = monomial
                if component_of[range_index] != component_of[source_index]:
                    continue
                if left == range_leaf and right.startswith(source_leaf) and len(right) == len(source_leaf) + 1:
                    edges.append({
                        "letter": letter_name,
                        "base": source_leaf,
                        "child": right,
                        "bridge_base": range_leaf,
                        "orientation": "child-to-base",
                    })
                if right == source_leaf and left.startswith(range_leaf) and len(left) == len(range_leaf) + 1:
                    edges.append({
                        "letter": letter_name,
                        "base": range_leaf,
                        "child": left,
                        "bridge_base": source_leaf,
                        "orientation": "base-to-child",
                    })
    unique = []
    seen = set()
    for edge in edges:
        key = tuple(edge.items())
        if key not in seen:
            seen.add(key)
            unique.append(edge)
    return unique


def value_key(value):
    return tuple(sorted((left, right, coefficient)
                        for (left, right), coefficient in value.items()))


def short_child_corners(q, letter, target_bits, max_depth=6):
    """Find direct child/base matrix-unit corners in short mixed words."""
    generators = (q, letter, leavitt_star(q), leavitt_star(letter))
    generator_names = ("q", "l", "q*", "l*")
    layer = [(ONE, ())]
    seen = {value_key(ONE)}
    hits = {}
    for depth in range(max_depth + 1):
        following = []
        for value, word in layer:
            for base in BASE_CODE:
                for bit in target_bits:
                    child = base + bit
                    forward = single_monomial(corner(child, value, base))
                    if forward == (child, base):
                        hits.setdefault((base, child), {
                            "orientation": "base-to-child",
                            "word": "1" if not word else " ".join(
                                generator_names[index] for index in word),
                            "depth": depth,
                        })
                    backward = single_monomial(corner(base, value, child))
                    if backward == (base, child):
                        hits.setdefault((base, child), {
                            "orientation": "child-to-base",
                            "word": "1" if not word else " ".join(
                                generator_names[index] for index in word),
                            "depth": depth,
                        })
            if depth == max_depth:
                continue
            for generator_index, generator in enumerate(generators):
                new_value = leavitt_mul(value, generator)
                key = value_key(new_value)
                if key not in seen:
                    seen.add(key)
                    following.append((new_value, word + (generator_index,)))
        layer = following
    return [
        {"base": base, "child": child, **certificate}
        for (base, child), certificate in sorted(hits.items())
    ], len(seen)


def combined_one_letter_scan(pairs):
    """Use all hard-pair units at once and test complementary branching."""
    named_values = []
    value_names = {}
    for pair_index, pair in enumerate(pairs):
        q, letter = pair[-2:]
        for suffix, value in (
                ("q", q), ("l", letter),
                ("q*", leavitt_star(q)), ("l*", leavitt_star(letter))):
            key = value_key(value)
            value_names.setdefault(key, []).append(f"pair{pair_index}:{suffix}")
            if all(value_key(old_value) != key for _, old_value in named_values):
                named_values.append((key, value))

    graph = {index: set() for index in range(len(BASE_CODE))}
    for _, value in named_values:
        matrix = chart_matrix(value, BASE_CODE)
        if matrix is None:
            continue
        value_graph = support_graph(matrix)
        for source, targets in value_graph.items():
            graph[source].update(targets)
    combined_components = []
    unseen = set(range(len(BASE_CODE)))
    while unseen:
        root = min(unseen)
        component = {root}
        queue = [root]
        while queue:
            vertex = queue.pop()
            for following in graph[vertex]:
                if following not in component:
                    component.add(following)
                    queue.append(following)
        combined_components.append(component)
        unseen -= component
    component_of = {
        vertex: component_index
        for component_index, component in enumerate(combined_components)
        for vertex in component
    }

    hits = []
    for key, value in named_values:
        for range_index, range_leaf in enumerate(BASE_CODE):
            for source_index, source_leaf in enumerate(BASE_CODE):
                if component_of[range_index] != component_of[source_index]:
                    continue
                monomial = single_monomial(corner(range_leaf, value, source_leaf))
                if monomial is None:
                    continue
                left, right = monomial
                if left == range_leaf and right.startswith(source_leaf) and len(right) == len(source_leaf) + 1:
                    hits.append({
                        "names": value_names[key], "base": source_leaf,
                        "child": right, "bridge_base": range_leaf,
                        "orientation": "child-to-base",
                    })
                if right == source_leaf and left.startswith(range_leaf) and len(left) == len(range_leaf) + 1:
                    hits.append({
                        "names": value_names[key], "base": range_leaf,
                        "child": left, "bridge_base": source_leaf,
                        "orientation": "base-to-child",
                    })
    children_by_base = {}
    for hit in hits:
        children_by_base.setdefault(hit["base"], set()).add(hit["child"])
    return {
        "distinct_generators": len(named_values),
        "base_components": [
            [BASE_CODE[index] for index in sorted(component)]
            for component in combined_components
        ],
        "child_corners": hits,
        "two_child_bases": sorted(
            base for base, children in children_by_base.items()
            if {base + "0", base + "1"} <= children),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-depth", type=int, required=True)
    parser.add_argument("--target-bit", choices=("0", "1"), action="append",
                        required=True)
    selection = parser.add_mutually_exclusive_group(required=True)
    selection.add_argument("--all-pairs", action="store_true")
    selection.add_argument("--pair-index", type=int, action="append")
    args = parser.parse_args()
    if args.max_depth < 0:
        parser.error("--max-depth must be nonnegative")
    target_bits = tuple(sorted(set(args.target_bit)))

    pairs = hard_pairs()
    if args.pair_index is not None:
        invalid = [index for index in args.pair_index
                   if index < 0 or index >= len(pairs)]
        if invalid:
            parser.error(f"--pair-index outside 0..{len(pairs) - 1}: {invalid}")
        selected_indices = sorted(set(args.pair_index))
        selected_pairs = [pairs[index] for index in selected_indices]
    else:
        selected_indices = list(range(len(pairs)))
        selected_pairs = pairs
    results = []
    for boundary_index, inverted, rotation, prefix_length, q, letter in selected_pairs:
        edges = child_edges(q, letter)
        short_corners, distinct_values = short_child_corners(
            q, letter, target_bits=target_bits, max_depth=args.max_depth)
        children_by_base = {}
        for edge in edges:
            children_by_base.setdefault(edge["base"], set()).add(edge["child"])
        two_children = sorted(
            base for base, children in children_by_base.items()
            if {base + "0", base + "1"} <= children
        )
        short_children_by_base = {}
        for edge in edges:
            short_children_by_base.setdefault(edge["base"], set()).add(
                edge["child"])
        for corner_certificate in short_corners:
            short_children_by_base.setdefault(
                corner_certificate["base"], set()).add(
                    corner_certificate["child"])
        short_two_children = sorted(
            base for base, children in short_children_by_base.items()
            if {base + "0", base + "1"} <= children
        )
        results.append({
            "boundary_index": boundary_index,
            "inverted": inverted,
            "rotation": rotation,
            "prefix_length": prefix_length,
            "child_edges": edges,
            "two_child_bases": two_children,
            "short_search_max_depth": args.max_depth,
            "short_search_distinct_values": distinct_values,
            "short_child_corners": short_corners,
            "short_two_child_bases": short_two_children,
        })
    print(json.dumps({
        "selected_pair_indices": selected_indices,
        "target_bits": target_bits,
        "pair_count": len(results),
        "all_pairs_have_two_children": all(r["two_child_bases"] for r in results),
        "all_pairs_have_short_two_children": all(
            r["short_two_child_bases"] for r in results),
        "combined_one_letter_scan": combined_one_letter_scan(selected_pairs),
        "results": results,
    }, indent=2))


if __name__ == "__main__":
    main()
