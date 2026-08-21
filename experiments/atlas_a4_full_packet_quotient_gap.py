#!/usr/bin/env python3
"""Emit a bounded GAP audit for the full A4 packet plus collision 19243.

The emitted presentation starts from two copies of the concrete matrix group
``GL(4,2) ~= A8``.  It then adjoins the thirty shortest mixed A4 pair-cubes
and the collision word 19243 as relators.  GAP constructs its own finite
presentation of each chart before taking the free product, so this exporter
does not depend on a hand-written presentation of ``A8``.

This is a discovery audit.  A finite quotient certificate would still have
to be exported and checked independently before it could be used in Cairn.
"""

import json
import os

from atlas_kernel_collision_enumerator import enumerate_ball, spanning_tree_kernel_words
from atlas_triangle_19243_packet import decode_word, select_triangle_packet, x_lengths
from atlas_two_chart_search import factor_generators


def gap_matrix(matrix):
    entries = ",".join(str(int(value)) for value in matrix.reshape(-1))
    return f"ImmutableMatrix(F2,4,4,[{entries}])"


def gap_word(word):
    factors = []
    for chart, matrix in word:
        embedding = "e1" if chart == 1 else "e2"
        factors.append(f"Image({embedding},Image(iso,{gap_matrix(matrix)}))")
    return "*".join(factors) if factors else "One(FP)"


def main():
    states, _ = enumerate_ball(5)
    words, _, _ = spanning_tree_kernel_words(states)
    packet = select_triangle_packet(words, x_lengths())

    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "atlas-word-19243.json"), encoding="utf-8") as handle:
        collision = decode_word(json.load(handle)[0]["word"])

    generators = [word[0][1] for _, word in factor_generators()[:6]]
    print('LoadPackage("kbmag");;')
    print("F2:=GF(2);;")
    print("G:=Group([%s]);;" % ",".join(gap_matrix(matrix) for matrix in generators))
    print("iso:=IsomorphismFpGroup(G);;")
    print("P:=Image(iso);;")
    print("FP:=FreeProduct(P,P);;")
    print("e1:=Embedding(FP,1);; e2:=Embedding(FP,2);;")
    relators = [gap_word(word) for _, word in packet]
    relators.append(gap_word(collision))
    print("mixed:=[%s];;" % ",\n".join(relators))
    print("Q:=FP/mixed;;")
    print('Print("chart_size ",Size(G),"\\n");')
    print('Print("mixed_relators ",Length(mixed),"\\n");')
    print("Qsmall:=SimplifiedFpGroup(Q);;")
    print('Print("simplified_generators ",Length(GeneratorsOfGroup(Qsmall)),"\\n");')
    print('Print("simplified_relators ",Length(RelatorsOfFpGroup(Qsmall)),"\\n");')
    print('Print("quotient_size ",Size(Qsmall),"\\n");')
    print("imgs:=List([1..Length(GeneratorsOfGroup(P))],i->Image(e1,GeneratorsOfGroup(P)[i])*One(Q));;")
    print('Print("first_chart_image_size ",Size(Group(imgs)),"\\n");')
    print("QUIT;")


if __name__ == "__main__":
    main()
