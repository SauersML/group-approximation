#!/usr/bin/env python3
"""Emit GAP for the exact quotient defined by the A4 packet and q_19243.

The quotient is

    (A8 * A8) / << thirty shortest A4 pair-cubes, q_19243 >>.

If it has order 20160, the known aligned map onto A8 identifies it with A8.
The exporter also tests four aligned bridge generators, so a run can still
produce useful normal-closure certificates when a full size computation is
too expensive.
"""

import argparse
import itertools
import json
import os

import numpy as np

from atlas_a4_packet_generation import select_packet, x_lengths
from atlas_a4_rank_three_core import H18_LABEL_HEX, center, matrix_key, packet_edge, subgroup
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word
from atlas_two_chart_search import I4, factor_generators, gf2_inv, gf2_mul


def gap_perm(matrix):
    vectors = [
        np.array(bits, dtype=np.uint8)
        for bits in itertools.product((0, 1), repeat=4)
        if any(bits)
    ]
    lookup = {tuple(vector.tolist()): index + 1 for index, vector in enumerate(vectors)}
    images = []
    for vector in vectors:
        image = (matrix @ vector) & 1
        images.append(lookup[tuple(image.tolist())])
    return "PermList([%s])" % ",".join(map(str, images))


def embedded_word(word):
    if not word:
        return "One(P)"
    return "*".join("i%d(%s)" % (factor, gap_perm(matrix)) for factor, matrix in word)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--skip-size", action="store_true")
    parser.add_argument(
        "--core",
        action="store_true",
        help="use only the fourteen rank-three packet relators",
    )
    args = parser.parse_args()

    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = [word for _index, word in select_packet(words, x_lengths())]
    if args.core:
        h18 = subgroup([
            np.frombuffer(bytes.fromhex(value), dtype=np.uint8).reshape(4, 4).copy()
            for value in H18_LABEL_HEX
        ])
        central_order_three = {
            matrix_key(value)
            for value in center(h18)
            if matrix_key(value) != matrix_key(I4)
        }
        packet = [
            word
            for word in packet
            if matrix_key(packet_edge(word)[2]) not in central_order_three
        ]
        assert len(packet) == 14

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as stream:
        collision = decode_word(json.load(stream)[0]["word"])
    relators = packet + [collision]

    generators = [word[0][1] for _, word in factor_generators()[:6]]
    print("G:=Group([%s]);;" % ",".join(gap_perm(generator) for generator in generators))
    print("iso:=IsomorphismFpGroup(G);; F:=Image(iso);;")
    print("P:=FreeProduct(F,F);;")
    print("e1:=Embedding(P,1);; e2:=Embedding(P,2);;")
    print("i1:=g->Image(e1,Image(iso,g));;")
    print("i2:=g->Image(e2,Image(iso,g));;")
    print("rels:=[")
    for word in relators:
        print("%s," % embedded_word(word))
    print("];;")
    print("raw:=P/rels;;")
    print("nat:=GroupHomomorphismByImages(P,raw,GeneratorsOfGroup(P),GeneratorsOfGroup(raw));;")
    print("simp:=IsomorphismSimplifiedFpGroup(raw);; Q:=Image(simp);;")
    print('Print("packet_relators %d\\n");' % len(packet))
    print('Print("collision_relators 1\\n");')
    print('Print("simplified_generators ",Length(GeneratorsOfGroup(Q)),"\\n");')
    print('Print("simplified_relators ",Length(RelatorsOfFpGroup(Q)),"\\n");')
    print("K1:=Image(simp,Image(nat,Image(e1,F)));;")
    print("K2:=Image(simp,Image(nat,Image(e2,F)));;")
    print('Print("first_factor_size ",Size(K1),"\\n");')
    print('Print("second_factor_size ",Size(K2),"\\n");')

    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    bridges = []
    for row, column in ((0, 1), (1, 0), (1, 2), (2, 1)):
        h = I4.copy()
        h[row, column] ^= 1
        aligned = gf2_mul(gf2_mul(alignment, h), alignment_inverse)
        bridges.append("i2(%s)*i1(%s)^-1" % (gap_perm(h), gap_perm(aligned)))
    print("bridges:=[%s];;" % ",".join(bridges))
    print("bridgeImages:=List(bridges,b->Image(simp,Image(nat,b)));;")
    print('Print("bridge_trivial ",List(bridgeImages,IsOne),"\\n");')
    if not args.skip_size:
        print('Print("quotient_size ",Size(Q),"\\n");')
    print("QUIT;")


if __name__ == "__main__":
    main()
