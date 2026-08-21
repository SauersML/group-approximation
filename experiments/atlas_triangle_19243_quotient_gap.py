#!/usr/bin/env python3
"""Emit GAP for the exact quotient of A8*A8 by the A4 packet and 19243.

This is a deliberately small algebraic falsification test for the analytic
holonomy programme.  If the thirty shortest pair-cubes together with the
single collision word normally kill either A8 free factor, the fixed packet
already gives a direct relator certificate and no multiplicity analysis is
needed.  If the factor survives, the output prevents us from confusing the
classical alignment collapse with an algebraic collapse of the universal
packet group.
"""

import itertools
import json
import os

import numpy as np

from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word, select_triangle_packet, x_lengths
from atlas_two_chart_search import factor_generators


def gap_perm(matrix):
    vectors = [
        np.array(bits, dtype=np.uint8)
        for bits in itertools.product((0, 1), repeat=4)
        if any(bits)
    ]
    lookup = {
        tuple(vector.tolist()): index + 1
        for index, vector in enumerate(vectors)
    }
    images = []
    for vector in vectors:
        image = (matrix @ vector) & 1
        images.append(lookup[tuple(image.tolist())])
    return "PermList([%s])" % ",".join(map(str, images))


def embedded_word(word):
    return "*".join(
        "i%d(%s)" % (factor, gap_perm(matrix))
        for factor, matrix in word
    )


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_triangle_packet(words, x_lengths())
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as handle:
        collision = decode_word(json.load(handle)[0]["word"])

    generators = [word[0][1] for _, word in factor_generators()[:6]]
    print("G:=Group([%s]);;" % ",".join(gap_perm(g) for g in generators))
    print('Print("a8_size ",Size(G),"\\n");')
    print("iso:=IsomorphismFpGroup(G);; F:=Image(iso);;")
    print("P:=FreeProduct(F,F);;")
    print("e1:=Embedding(P,1);; e2:=Embedding(P,2);;")
    print("i1:=g->Image(e1,Image(iso,g));;")
    print("i2:=g->Image(e2,Image(iso,g));;")
    relators = [word for _, word in packet] + [collision]
    print('Print("relators ",%d,"\\n");' % len(relators))
    print("rels:=[%s];;" % ",".join(embedded_word(word) for word in relators))
    print("raw:=P/rels;;")
    print("nat:=GroupHomomorphismByImages(P,raw,GeneratorsOfGroup(P),GeneratorsOfGroup(raw));;")
    print("simp:=IsomorphismSimplifiedFpGroup(raw);; Q:=Image(simp);;")
    print('Print("simplified_generators ",Length(GeneratorsOfGroup(Q)),"\\n");')
    print('Print("simplified_relators ",Length(RelatorsOfFpGroup(Q)),"\\n");')
    print("K1:=Group(List(GeneratorsOfGroup(F),g->Image(simp,Image(nat,Image(e1,g)))));;")
    print("K2:=Group(List(GeneratorsOfGroup(F),g->Image(simp,Image(nat,Image(e2,g)))));;")
    print('Print("first_factor_size ",Size(K1),"\\n");')
    print('Print("second_factor_size ",Size(K2),"\\n");')
    print('Print("quotient_size ",Size(Q),"\\n");')
    print("QUIT;")


if __name__ == "__main__":
    main()
