#!/usr/bin/env python3
"""Export the exact affine-parabolic completion behind the 14-word A4 core.

The retained rank-three packet and collision 19243 never use the central C3
which leaves the affine parabolic.  Every syllable therefore belongs to

    P = AGL(3,2) < GL(4,2),  |P| = 1344.

This script verifies that support statement and emits a GAP presentation of

    (P * P) / << fourteen core pair-cubes, q_19243 >>.

It is deliberately an exporter rather than a local quotient computation.  The
presentation can be sent to MSI, where GAP's coset, rewriting, and finite-
quotient routines can be tried without using workstation RAM.
"""

import argparse
import itertools
import json
import os

import numpy as np

from atlas_a4_19243_component_localization import (
    H6_LABELS,
    Q_FIRST_INVOLUTION,
    Q_SECOND,
    mul,
    subgroup,
)
from atlas_a4_packet_19243_quotient import embedded_word, gap_perm
from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_a4_rank_three_core import H18_LABEL_HEX, matrix_key, packet_edge
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import I4, gf2_inv, gf2_mul


RELATIVE_GL5_HEX = "00000000010100000000000001000000000001000001000100"


def numpy_matrix(value):
    return np.asarray(value, dtype=np.uint8)


def center(group):
    return {left for left in group if all(mul(left, right) == mul(right, left) for right in group)}


def core_and_collision():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = [word for _index, word in select_packet(words, x_lengths())]

    h18 = subgroup([
        tuple(tuple(int(bit) for bit in row) for row in numpy_matrix(
            np.frombuffer(bytes.fromhex(value), dtype=np.uint8).reshape(4, 4)
        ))
        for value in H18_LABEL_HEX
    ])
    central_order_three = {
        bytes(numpy_matrix(value).reshape(-1))
        for value in center(h18)
        if value != tuple(tuple(int(i == j) for j in range(4)) for i in range(4))
    }
    core = [
        word for word in packet
        if matrix_key(packet_edge(word)[2]) not in central_order_three
    ]
    assert len(core) == 14

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    return core, collision


def parabolic():
    generators = tuple(H6_LABELS) + tuple(Q_SECOND) + (Q_FIRST_INVOLUTION,)
    values = subgroup(generators)
    assert len(values) == 1344
    return {bytes(numpy_matrix(value).reshape(-1)): numpy_matrix(value) for value in values}


def gap_perm_dimension(matrix):
    dimension = matrix.shape[0]
    vectors = [
        np.array(bits, dtype=np.uint8)
        for bits in itertools.product((0, 1), repeat=dimension)
        if any(bits)
    ]
    lookup = {tuple(vector.tolist()): index + 1 for index, vector in enumerate(vectors)}
    images = [
        lookup[tuple(((matrix @ vector) & 1).tolist())]
        for vector in vectors
    ]
    return "PermList([%s])" % ",".join(map(str, images))


def emit_finite_witness_image():
    relative = np.frombuffer(
        bytes.fromhex(RELATIVE_GL5_HEX), dtype=np.uint8
    ).reshape(5, 5)
    # Exact Gaussian elimination over F2 for the fixed 5-by-5 certificate.
    augmented = np.concatenate((relative.copy(), np.eye(5, dtype=np.uint8)), axis=1)
    for column in range(5):
        pivot = next(row for row in range(column, 5) if augmented[row, column])
        augmented[[column, pivot]] = augmented[[pivot, column]]
        for row in range(5):
            if row != column and augmented[row, column]:
                augmented[row] ^= augmented[column]
    relative_inverse = augmented[:, 5:]

    generators = [numpy_matrix(value) for value in tuple(H6_LABELS) + tuple(Q_SECOND)]
    generators.append(numpy_matrix(Q_FIRST_INVOLUTION))
    first = []
    second = []
    for generator in generators:
        embedded = np.eye(5, dtype=np.uint8)
        embedded[:4, :4] = generator
        first.append(embedded)
        second.append((relative @ embedded @ relative_inverse) & 1)

    print("P1:=Group([%s]);;" % ",".join(gap_perm_dimension(value) for value in first))
    print("P2:=Group([%s]);;" % ",".join(gap_perm_dimension(value) for value in second))
    print("W:=Group(Concatenation(GeneratorsOfGroup(P1),GeneratorsOfGroup(P2)));;")
    print('Print("P1_size ",Size(P1),"\\n");')
    print('Print("P2_size ",Size(P2),"\\n");')
    print('Print("intersection_size ",Size(Intersection(P1,P2)),"\\n");')
    print('Print("generated_image_size ",Size(W),"\\n");')
    print("QUIT;")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-size", action="store_true")
    parser.add_argument(
        "--finite-witness-image",
        action="store_true",
        help="emit GAP for the two affine parabolics in the GL5 countermodel",
    )
    args = parser.parse_args()

    if args.finite_witness_image:
        emit_finite_witness_image()
        return

    core, collision = core_and_collision()
    p = parabolic()
    for word in core + [collision]:
        for _factor, value in word:
            assert matrix_key(value) in p

    h_values = subgroup(tuple(H6_LABELS) + tuple(Q_SECOND))
    assert len(h_values) == 168
    reference = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    reference_inverse = gf2_inv(reference)
    aligned_h = {
        matrix_key(gf2_mul(gf2_mul(reference, numpy_matrix(value)), reference_inverse))
        for value in h_values
    }
    raw_h = {bytes(numpy_matrix(value).reshape(-1)) for value in h_values}
    print("# raw_H_order 168")
    print("# aligned_H_order 168")
    print("# raw_aligned_H_intersection %d" % len(raw_h & aligned_h))
    print("# aligned_H_inside_P %s" % (aligned_h <= set(p)))

    generators = [numpy_matrix(value) for value in tuple(H6_LABELS) + tuple(Q_SECOND)]
    generators.append(numpy_matrix(Q_FIRST_INVOLUTION))
    print("G:=Group([%s]);;" % ",".join(gap_perm(value) for value in generators))
    print('Print("parabolic_size ",Size(G),"\\n");')
    print("iso:=IsomorphismFpGroup(G);; F:=Image(iso);;")
    print("P:=FreeProduct(F,F);;")
    print("e1:=Embedding(P,1);; e2:=Embedding(P,2);;")
    print("i1:=g->Image(e1,Image(iso,g));;")
    print("i2:=g->Image(e2,Image(iso,g));;")
    print("rels:=[")
    for word in core + [collision]:
        print("%s," % embedded_word(word))
    print("];;")
    print("Q:=P/rels;;")
    print('Print("core_relators 14\\ncollision_relators 1\\n");')
    print('Print("fp_generators ",Length(GeneratorsOfGroup(Q)),"\\n");')
    print('Print("fp_relators ",Length(RelatorsOfFpGroup(Q)),"\\n");')
    if not args.skip_size:
        print('Print("quotient_size ",Size(Q),"\\n");')
    print("QUIT;")


if __name__ == "__main__":
    main()
