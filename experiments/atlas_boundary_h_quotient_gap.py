"""Emit the five-word rank-three quotient ``(H*H)/<<q_i>>`` for GAP.

The exact all-irrep greedy certificate selects boundary indices
``0,11,30,44,55``.  After transporting the second chart through ``k0``, every
syllable of these five words lies in ``H=diag(GL(3,2),1)``.  This exporter
therefore performs the normal-generation audit in ``H*H`` rather than in
``A8*A8``.  If the quotient has order 168 and the diagonal map onto H is
surjective, the five words normally generate precisely the kernel of the
fold map ``H*H -> H``.
"""

import argparse
import itertools

import numpy as np

from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import I4, gf2_inv, gf2_mul


INDICES = (0, 11, 30, 44, 55)
H_GENERATORS = ((0, 1), (1, 0), (1, 2), (2, 1))


def lies_in_h(matrix):
    expected = I4.copy()
    expected[:3, :3] = matrix[:3, :3]
    return np.array_equal(matrix, expected)


def gap_perm(matrix):
    vectors = [np.array(bits, dtype=np.uint8)
               for bits in itertools.product((0, 1), repeat=4)
               if any(bits)]
    lookup = {tuple(vector.tolist()): index + 1
              for index, vector in enumerate(vectors)}
    return "PermList([%s])" % ",".join(str(lookup[tuple(
        ((matrix @ vector) & 1).tolist())]) for vector in vectors)


def transported_word(word, alignment, alignment_inverse):
    result = []
    for factor, matrix in word:
        image = matrix if factor == 1 else gf2_mul(
            gf2_mul(alignment, matrix), alignment_inverse)
        if not lies_in_h(image):
            raise AssertionError("five-word packet escaped H")
        result.append((factor, image))
    return result


def embedded_word(word):
    return "*".join("i%d(%s)" % (factor, gap_perm(matrix))
                    for factor, matrix in word)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--all-h", action="store_true")
    parser.add_argument("--index-only", action="store_true")
    args = parser.parse_args()
    generators = []
    for row, column in H_GENERATORS:
        element = I4.copy()
        element[row, column] ^= 1
        generators.append(element)
    print("H:=Group([%s]);;" % ",".join(map(gap_perm, generators)))
    print('Print("h_size ",Size(H),"\\n");')
    print("iso:=IsomorphismFpGroup(H);; F:=Image(iso);;")
    print('Print("fp_generators ",GeneratorsOfGroup(F),"\\n");')
    print('Print("fp_relators ",RelatorsOfFpGroup(F),"\\n");')
    print("P:=FreeProduct(F,F);;")
    print("e1:=Embedding(P,1);; e2:=Embedding(P,2);;")
    print("i1:=g->Image(e1,Image(iso,g));;")
    print("i2:=g->Image(e2,Image(iso,g));;")
    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    words = boundary_words()
    if args.all_h:
        relators = []
        selected_indices = []
        for index, word in enumerate(words):
            try:
                relators.append(transported_word(
                    word, alignment, alignment_inverse))
                selected_indices.append(index)
            except AssertionError:
                pass
    else:
        selected_indices = list(INDICES)
        relators = [transported_word(
            words[index], alignment, alignment_inverse) for index in INDICES]
    print('Print("selected_relators %d\\n");' % len(relators))
    print("rels:=[%s];;" % ",".join(map(embedded_word, relators)))
    print("Q:=P/rels;;")
    print("nat:=GroupHomomorphismByImages(P,Q,GeneratorsOfGroup(P),"
          "GeneratorsOfGroup(Q));;")
    print("K:=Group(List(GeneratorsOfGroup(F),g->Image(nat,Image(e1,g))));;")
    print('Print("first_factor_index ",Index(Q,K),"\\n");')
    if not args.index_only:
        print('Print("quotient_size ",Size(Q),"\\n");')
    print("QUIT;")


if __name__ == "__main__":
    main()
