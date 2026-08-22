#!/usr/bin/env python3
"""Verify the exact GL5(F2) countermodel to the fourteen-word A4 core.

The fixed relative chart matrix was found by the exhaustive coset screen in
``atlas_a4_gl5_packet_screen.py --core --first-collision-survivor``.  This
small verifier does not repeat that search: it checks the resulting finite
certificate directly with exact arithmetic over F2.
"""

import json

import numpy as np

from atlas_a4_gl5_packet_screen import (
    I5,
    collision_value,
    embed4,
    inv5,
    key5,
    mul5,
    order5,
)
from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_a4_parabolic_completion import core_and_collision
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_t30_parabolic_c3_bridge import H6_LABELS, Q_SECOND


RELATIVE_HEX = "00000000010100000000000001000000000001000001000100"


def cube_holds(word, relative):
    value = collision_value(word, relative)
    return np.array_equal(mul5(mul5(value, value), value), I5)


def main():
    relative = np.frombuffer(bytes.fromhex(RELATIVE_HEX), dtype=np.uint8).reshape(5, 5)
    relative_inverse = inv5(relative)

    core, collision = core_and_collision()
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    full_packet = [word for _index, word in select_packet(words, x_lengths())]

    core_checks = [cube_holds(word, relative) for word in core]
    full_checks = [cube_holds(word, relative) for word in full_packet]
    collision_value_at_relative = collision_value(collision, relative)

    moved_rank_three = []
    rank_three_labels = [
        (f"H6[{index}]", np.asarray(label, dtype=np.uint8))
        for index, label in enumerate(H6_LABELS)
    ] + [
        (f"Q_SECOND[{index}]", np.asarray(label, dtype=np.uint8))
        for index, label in enumerate(Q_SECOND)
    ]
    for label_name, label in rank_three_labels:
        image = embed4(label)
        cocycle = mul5(
            mul5(mul5(relative, image), relative_inverse),
            inv5(image),
        )
        if not np.array_equal(cocycle, I5):
            moved_rank_three.append({
                "label": label_name,
                "cocycle_hex": key5(cocycle).hex(),
                "cocycle_order": order5(cocycle),
            })

    assert len(core) == 14
    assert all(core_checks)
    assert sum(full_checks) == 14
    assert len(full_packet) == 30
    assert np.array_equal(collision_value_at_relative, I5)
    assert len(moved_rank_three) == len(rank_three_labels)

    print(json.dumps({
        "ambient_group": "GL5(F2)",
        "ambient_order": 9999360,
        "chart_group": "diag(GL4(F2),1)",
        "chart_index": 496,
        "collision_19243_value_hex": key5(collision_value_at_relative).hex(),
        "core_relations_satisfied": sum(core_checks),
        "core_relations_total": len(core_checks),
        "full_packet_relations_satisfied": sum(full_checks),
        "full_packet_relations_total": len(full_checks),
        "moved_rank_three_generators": moved_rank_three,
        "relative_chart_matrix_hex": RELATIVE_HEX,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
