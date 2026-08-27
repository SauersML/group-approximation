#!/usr/bin/env python3
"""Exact C3-line connection spectrum for the two rank-three A4 components.

The fourteen-word A4 core consists of two S3 components H6 and K generating
H=GL3(2).  On Reg(H), let P_i be averaging over the order-three subgroup of
the i-th S3.  In the normalized left-coset basis for ran(P_0), the compression
P_0 P_1 P_0 is B/9 for an integer 56 by 56 matrix B.  This script verifies
the minimal polynomial and exact power traces of B using integer arithmetic.
"""

import json
import sys

import numpy as np

from atlas_a4_packet_component_audit import center, subgroup
from atlas_a4_packet_generation import matrix_order, select_packet, x_lengths
from atlas_a4_rank_three_core import H18_LABEL_HEX, components, matrix, packet_edge
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_two_chart_search import I4, gf2_mul, matrix_key


def polynomial_product(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return out


def predicted_power_sum(power):
    def quadratic_sum(a, b):
        if power == 0:
            return 2
        old, value = 2, a
        for _ in range(2, power + 1):
            old, value = value, a * value - b * old
        return value

    if power == 0:
        return 56
    return (
        9**power
        + 12 * 2**power
        + 6 * 4**power
        + 8 * quadratic_sum(6, 1)
        + 7 * quadratic_sum(9, 16)
    )


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_packet(words, x_lengths())

    h18 = subgroup([matrix(value) for value in H18_LABEL_HEX])
    central_order_three = {
        matrix_key(value)
        for value in center(h18)
        if matrix_key(value) != matrix_key(I4)
    }
    core = []
    for index, word in packet:
        factor, b, a = packet_edge(word)
        if matrix_key(a) not in central_order_three:
            core.append((index, factor, b, a))

    comps, matrices = components(core)
    s3_groups = [subgroup([matrices[key] for key in comp]) for comp in comps]
    h_group = subgroup(list(s3_groups[0].values()) + list(s3_groups[1].values()))
    assert len(h_group) == 168

    c3_groups = []
    for group in s3_groups:
        c3 = [value for value in group.values() if matrix_order(value) in (1, 3)]
        assert len(c3) == 3
        c3_groups.append(c3)
    assert len(subgroup(c3_groups[0] + c3_groups[1])) == 168

    h_keys = sorted(h_group)
    h_sets = {key: h_group[key] for key in h_keys}
    unseen = set(h_keys)
    cosets = []
    while unseen:
        representative = min(unseen)
        coset = {
            matrix_key(gf2_mul(a, h_sets[representative]))
            for a in c3_groups[0]
        }
        assert len(coset) == 3
        cosets.append(coset)
        unseen -= coset
    assert len(cosets) == 56

    b_matrix = np.zeros((56, 56), dtype=np.int64)
    for column, source in enumerate(cosets):
        for h in c3_groups[1]:
            moved = {
                matrix_key(gf2_mul(h, h_sets[value]))
                for value in source
            }
            for row, target in enumerate(cosets):
                b_matrix[row, column] += len(target & moved)
    assert np.array_equal(b_matrix, b_matrix.T)

    factors = (
        [0, 1],
        [-9, 1],
        [-2, 1],
        [-4, 1],
        [1, -6, 1],
        [16, -9, 1],
    )
    polynomial = [1]
    for factor in factors:
        polynomial = polynomial_product(polynomial, factor)

    identity = np.eye(56, dtype=np.int64)
    value = np.zeros((56, 56), dtype=np.int64)
    power_matrix = identity.copy()
    for coefficient in polynomial:
        value += coefficient * power_matrix
        power_matrix = power_matrix @ b_matrix
    assert not np.any(value)

    traces = []
    power_matrix = identity.copy()
    for power in range(9):
        trace = int(np.trace(power_matrix))
        assert trace == predicted_power_sum(power)
        traces.append(trace)
        power_matrix = power_matrix @ b_matrix

    print(json.dumps({
        "group": "GL3(2)",
        "group_order": 168,
        "c3_fixed_rank": 56,
        "intersection_rank": 1,
        "compression": "P0 P1 P0 = B/9",
        "spectrum": {
            "0": 7,
            "1": 1,
            "2/9": 12,
            "4/9": 6,
            "1/3-2sqrt(2)/9": 8,
            "1/3+2sqrt(2)/9": 8,
            "1/2-sqrt(17)/18": 7,
            "1/2+sqrt(17)/18": 7,
        },
        "largest_nontrivial_eigenvalue": "1/2+sqrt(17)/18",
        "line_connection_gap": "1/2-sqrt(17)/18=(9-sqrt(17))/18",
        "integer_power_traces_0_through_8": traces,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    sys.exit(main())

