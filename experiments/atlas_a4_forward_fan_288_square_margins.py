#!/usr/bin/env python3
"""Exact regular-multiplicity audit for the remaining 288-point square."""

import json


def restriction_multiplicity(copies, group_order, subgroup_order):
    return copies * group_order // subgroup_order


def main():
    degree = 288
    vertices = {
        "Q96": (96, 3),
        "F36": (36, 8),
        "J24": (24, 12),
        "C144": (144, 2),
    }
    assert all(order * copies == degree for order, copies in vertices.values())

    edges = {
        "Q96_F36_V4": ("Q96", "F36", 4),
        "Q96_J24_A4": ("Q96", "J24", 12),
        "F36_C144_C3xC3": ("F36", "C144", 9),
        "J24_C144_C2": ("J24", "C144", 2),
    }
    multiplicities = {}
    for name, (left, right, subgroup_order) in edges.items():
        left_order, left_copies = vertices[left]
        right_order, right_copies = vertices[right]
        left_multiplicity = restriction_multiplicity(
            left_copies, left_order, subgroup_order)
        right_multiplicity = restriction_multiplicity(
            right_copies, right_order, subgroup_order)
        assert left_multiplicity == right_multiplicity
        multiplicities[name] = left_multiplicity

    print(json.dumps({
        "ambient_permutation_degree": degree,
        "vertex_regular_copies": {name: copies for name, (_order, copies) in vertices.items()},
        "vertex_orders": {name: order for name, (order, _copies) in vertices.items()},
        "edge_regular_multiplicities": multiplicities,
        "cycle_rank": 1,
        "unresolved_condition": "one permutation double coset around the four-vertex square",
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
