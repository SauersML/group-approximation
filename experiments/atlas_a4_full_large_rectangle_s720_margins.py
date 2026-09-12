#!/usr/bin/env python3
"""Regular-multiplicity audit for the full large-rectangle finite atlas."""

import json


def main():
    degree = 720
    vertices = {
        "large_rectangle_A5": (60, 12),
        "first_packet_S3xS3": (36, 20),
        "collision_S4": (24, 30),
        "forward_fan_C144": (144, 5),
    }
    assert all(order * copies == degree for order, copies in vertices.values())
    edges = {
        "rectangle_first_packet_S3": ("large_rectangle_A5", "first_packet_S3xS3", 6),
        "rectangle_collision_S3": ("large_rectangle_A5", "collision_S4", 6),
        "first_packet_forward_A9": ("first_packet_S3xS3", "forward_fan_C144", 9),
        "collision_forward_B2": ("collision_S4", "forward_fan_C144", 2),
        "first_packet_collision_c2": ("first_packet_S3xS3", "collision_S4", 2),
    }
    multiplicities = {}
    for name, (left, right, edge_order) in edges.items():
        left_order, left_copies = vertices[left]
        right_order, right_copies = vertices[right]
        left_multiplicity = left_copies * left_order // edge_order
        right_multiplicity = right_copies * right_order // edge_order
        assert left_multiplicity == right_multiplicity
        multiplicities[name] = left_multiplicity
    print(json.dumps({
        "ambient_permutation_degree": degree,
        "vertex_orders": {name: value[0] for name, value in vertices.items()},
        "vertex_regular_copies": {name: value[1] for name, value in vertices.items()},
        "edge_regular_multiplicities": multiplicities,
        "graph_vertices": 4,
        "graph_edges": 5,
        "cycle_rank": 2,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
