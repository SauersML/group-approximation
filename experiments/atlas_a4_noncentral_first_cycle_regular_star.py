#!/usr/bin/env python3
"""Multiplicity certificate for the noncentral Q96 regular-star carrier."""

import json


def main():
    core = 96
    first_packet = 36
    collision_packet = 24
    overlap_first = 4
    overlap_collision = 12
    core_copies = 3
    first_copies = 8
    collision_copies = 12

    degree = core_copies * core
    assert degree == first_copies * first_packet == collision_copies * collision_packet == 288
    assert core_copies * (core // overlap_first) == first_copies * (
        first_packet // overlap_first) == 72
    assert core_copies * (core // overlap_collision) == collision_copies * (
        collision_packet // overlap_collision) == 24

    print(json.dumps({
        "ambient_permutation_degree": degree,
        "Q_core_order": core,
        "first_packet_vertex_order": first_packet,
        "collision_S4_vertex_order": collision_packet,
        "V4_overlap_order": overlap_first,
        "A4_overlap_order": overlap_collision,
        "Q_regular_copies": core_copies,
        "first_packet_regular_copies": first_copies,
        "collision_packet_regular_copies": collision_copies,
        "V4_regular_multiplicity": 72,
        "A4_regular_multiplicity": 24,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
