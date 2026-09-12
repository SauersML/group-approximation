#!/usr/bin/env python3
"""Exact calibration for the short atlas kernel word at tree index 14.

In the radius-five spanning-tree kernel enumeration, word 14 is

    q14 = (t23_(1) t23_(2))^2.

After the fixed inner A4-packet reference alignment R, the second-chart
coefficient t23 becomes t30.  Thus, in the amplified regular representation,

    q14(U) = (rho(t23) U rho(t30) U*)^2.

Every U commuting with rho(t30) gives q14(U)=rho(t20), a nonidentity
involution.  This is the exact finite input for the normalized-HS wall proved
in Cairn by ``atlas-q14-forces-t30-covariance-floor``.

The final enumeration is also a no-shortcut audit.  The A4 packet together
with q14 still has exact classical alignments, so q14 cannot replace collision
19243 as the packet escape-killer.
"""

import json

import numpy as np

from atlas_a4_reference_alignment import EXPECTED_HEX
from atlas_boundary_inner_alignment import enumerate_gl4
from atlas_kernel_collision_enumerator import (
    enumerate_ball,
    evaluate_word,
    leavitt_is_one,
    spanning_tree_kernel_words,
)
from atlas_triangle_19243_packet import (
    aligned_value,
    select_triangle_packet,
    x_lengths,
)
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, matrix_key


TREE_INDEX = 14
T23_HEX = "01000000000100000000010100000001"
T30_HEX = "01000000000100000000010001000001"
T20_HEX = "01000000000100000100010000000001"


def matrix_from_hex(value: str) -> np.ndarray:
    raw = bytes.fromhex(value)
    if len(raw) != 16:
        raise ValueError("expected one 4 by 4 F2 matrix")
    return np.frombuffer(raw, dtype=np.uint8).reshape(4, 4).copy()


def matrix_order(matrix: np.ndarray) -> int:
    value = I4.copy()
    for exponent in range(1, 16):
        value = gf2_mul(value, matrix)
        if matrix_key(value) == matrix_key(I4):
            return exponent
    raise AssertionError("element order exceeds GL(4,2) bound")


def main() -> None:
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    q14 = words[TREE_INDEX]

    t23 = matrix_from_hex(T23_HEX)
    t30 = matrix_from_hex(T30_HEX)
    t20 = matrix_from_hex(T20_HEX)
    identity = matrix_key(I4)

    assert len(q14) == 4
    assert [factor for factor, _ in q14] == [1, 2, 1, 2]
    assert all(matrix_key(matrix) == matrix_key(t23) for _, matrix in q14)
    assert leavitt_is_one(evaluate_word(q14))

    reference = matrix_from_hex(EXPECTED_HEX)
    reference_inverse = gf2_inv(reference)
    aligned_t23 = gf2_mul(gf2_mul(reference, t23), reference_inverse)
    assert matrix_key(aligned_t23) == matrix_key(t30)
    reference_value = aligned_value(
        q14, reference, reference_inverse, use_outer=False
    )
    assert reference_value == matrix_key(t20)
    assert reference_value != identity
    assert matrix_order(t20) == 2

    packet = select_triangle_packet(words, x_lengths())
    counts = {}
    for use_outer in (False, True):
        packet_survivors = 0
        q14_survivors = 0
        combined_survivors = 0
        for alignment in enumerate_gl4():
            inverse = gf2_inv(alignment)
            packet_holds = all(
                aligned_value(word, alignment, inverse, use_outer) == identity
                for _, word in packet
            )
            q14_holds = (
                aligned_value(q14, alignment, inverse, use_outer) == identity
            )
            packet_survivors += int(packet_holds)
            q14_survivors += int(q14_holds)
            combined_survivors += int(packet_holds and q14_holds)
        label = "outer" if use_outer else "inner"
        counts[label] = {
            "packet_survivors": packet_survivors,
            "q14_survivors": q14_survivors,
            "packet_plus_q14_survivors": combined_survivors,
        }

    expected = {
        "inner": {
            "packet_survivors": 30,
            "q14_survivors": 4800,
            "packet_plus_q14_survivors": 11,
        },
        "outer": {
            "packet_survivors": 30,
            "q14_survivors": 4800,
            "packet_plus_q14_survivors": 10,
        },
    }
    if counts != expected:
        raise AssertionError(f"q14 calibration changed: {counts}")

    print(json.dumps({
        "tree_index": TREE_INDEX,
        "word": "(t23_(1) t23_(2))^2",
        "free_product_syllable_length": len(q14),
        "is_exact_leavitt_kernel_word": True,
        "reference_alignment_hex": EXPECTED_HEX,
        "reference_alignment_conjugates_t23_to": "t30",
        "reference_aligned_value": "t20",
        "reference_aligned_value_order": matrix_order(t20),
        "normalized_hs_constants": {
            "relative_unitary_lipschitz_constant": 4,
            "distance_to_t30_commutant_squared_floor": "1/8",
            "sharp_t30_covariance_defect_squared_floor": "1",
            "sharp_root_energy_x30_squared_floor": "1/2",
            "robust_root_energy_loss_coefficient": "1+sqrt(2)",
        },
        "classical_no_shortcut_audit": counts,
    }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
