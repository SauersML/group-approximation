#!/usr/bin/env python3
"""Exact two-holonomy profile on all sixty classical packet alignments.

The thirty shortest A4 pair-cubes have thirty inner and thirty outer
automorphism alignments.  For each alignment this script evaluates collision
19243 and the bridge covariances ``c=h*k`` and ``a=z*b`` in the natural
15-point permutation character of ``A8=GL(4,2)``.  All arithmetic is exact
over F2; the reported defect numerators are integers divided by 15.
"""

import collections
import json
import os

import numpy as np

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_t30_parabolic_c3_bridge import (
    H6_LABELS,
    H18_LABELS,
    I4 as I4_TUPLE,
    Q_FIRST_INVOLUTION,
    Q_SECOND,
    center,
    matrix_hex,
    subgroup,
)
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


def outer(matrix):
    return gf2_inv(matrix).T.copy()


def transformed(matrix, alignment, inverse, use_outer):
    source = outer(matrix) if use_outer else matrix
    return gf2_mul(gf2_mul(alignment, source), inverse)


def word_value(word, alignment, inverse, use_outer):
    value = I4.copy()
    for factor, matrix in word:
        image = transformed(matrix, alignment, inverse, use_outer) if factor == 2 else matrix
        value = gf2_mul(value, image)
    return value


def nonzero_fixed_points(matrix):
    count = 0
    for value in range(1, 16):
        vector = np.array([(value >> bit) & 1 for bit in range(4)], dtype=np.uint8)
        count += int(np.array_equal((matrix @ vector) & 1, vector))
    return count


def defect_numerator(matrix):
    """Return 15*||P(matrix)-I||_2^2 in the 15-point action."""
    return 2 * (15 - nonzero_fixed_points(matrix))


def bridge_labels():
    h = np.array(H6_LABELS[2], dtype=np.uint8)
    k = np.array(Q_SECOND[0], dtype=np.uint8)
    c = gf2_mul(h, k)
    h18 = subgroup(H18_LABELS)
    z_values = sorted(
        (value for value in center(h18) if value != I4_TUPLE),
        key=matrix_hex,
    )
    z = np.array(z_values[0], dtype=np.uint8)
    b = np.array(Q_FIRST_INVOLUTION, dtype=np.uint8)
    return c, gf2_mul(z, b)


def audit(packet, collision, use_outer):
    identity = matrix_key(I4)
    c, a = bridge_labels()
    joint = collections.Counter()
    alignments = []
    for alignment in enumerate_gl4():
        inverse = gf2_inv(alignment)
        if not all(
            matrix_key(word_value(word, alignment, inverse, use_outer)) == identity
            for _index, word in packet
        ):
            continue
        q_value = word_value(collision, alignment, inverse, use_outer)
        c_cocycle = gf2_mul(
            transformed(c, alignment, inverse, use_outer), gf2_inv(c)
        )
        a_cocycle = gf2_mul(
            transformed(a, alignment, inverse, use_outer), gf2_inv(a)
        )
        q_num = defect_numerator(q_value)
        energy_num = 2 * defect_numerator(c_cocycle) + defect_numerator(a_cocycle)
        joint[(energy_num, q_num)] += 1
        alignments.append({
            "alignment_hex": matrix_key(alignment).hex(),
            "two_holonomy_energy_numerator_over_15": energy_num,
            "collision_defect_squared_numerator_over_15": q_num,
        })

    if len(alignments) != 30:
        raise AssertionError("classical packet survivor count changed: %d" % len(alignments))
    if any(q_num == 0 for _energy_num, q_num in joint):
        raise AssertionError("collision survived a classical packet alignment")

    maximum_ratio = max(
        (energy_num / q_num, energy_num, q_num)
        for energy_num, q_num in joint
    )
    return {
        "packet_alignments": len(alignments),
        "joint_histogram": {
            "E2_num=%d,q_defect2_num=%d" % pair: count
            for pair, count in sorted(joint.items())
        },
        "maximum_ratio": {
            "value": maximum_ratio[0],
            "energy_numerator": maximum_ratio[1],
            "collision_numerator": maximum_ratio[2],
        },
        "sharp_E2_le_5_qdef2_count": sum(
            count for (energy_num, q_num), count in joint.items()
            if energy_num == 5 * q_num
        ),
        "alignments": alignments,
    }


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])

    output = {
        "representation": "15-point action of GL4(F2) on nonzero vectors",
        "normalization_denominator": 15,
        "inequality_tested": "E_2HOL <= 5 ||q_19243-I||_2^2",
        "inner": audit(packet, collision, False),
        "outer": audit(packet, collision, True),
    }
    output["E2_le_5_qdef2"] = {
        branch: output[branch]["maximum_ratio"]["value"] <= 5
        for branch in ("inner", "outer")
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
