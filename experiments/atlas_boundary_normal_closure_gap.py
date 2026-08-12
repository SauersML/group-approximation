"""Emit a GAP audit of the *actual* atlas boundary-centrality quotient.

Let ``P=A8*A8``.  For every one of the 234 first-boundary collision words
``q`` and every generator ``s`` of either free factor, impose ``[s,q]=1``.
These, rather than ``q=1``, are the relations supplied by the canonical
atlas criterion.  The unique classical solution sends the second factor
through conjugation by ``k0``.  This exporter asks GAP for the size of the
resulting finitely presented quotient and tests the four bridge words

    i2(h) i1(k0 h k0^-1)^-1

for adjacent transvections generating ``H=diag(GL(3,2),1)``.

If the quotient has order 20160, the classical map onto ``A8`` proves that
it is exactly ``A8`` and all four bridges lie in the normal closure of the
genuine boundary relators.  Even if the quotient is larger, GAP may still
certify the individual bridge words.  Free-product words are deduplicated
before export because the raw packet has 234*12 entries.
"""

import argparse
import itertools

import numpy as np

from atlas_boundary_group_algebra_audit import matrix_from_key
from atlas_boundary_h_tangent_screen import INNER_ALIGNMENT_HEX
from atlas_certified_a8_alignment import boundary_words
from atlas_two_chart_search import (
    I4,
    commutator,
    factor_generators,
    gf2_inv,
    gf2_mul,
)


def gap_perm(matrix):
    vectors = [np.array(bits, dtype=np.uint8)
               for bits in itertools.product((0, 1), repeat=4)
               if any(bits)]
    lookup = {tuple(vector.tolist()): index + 1
              for index, vector in enumerate(vectors)}
    images = []
    for vector in vectors:
        image = (matrix @ vector) & 1
        images.append(lookup[tuple(image.tolist())])
    return "PermList([%s])" % ",".join(map(str, images))


def embedded_word(word):
    if not word:
        return "One(P)"
    return "*".join(
        "i%d(%s)" % (factor, gap_perm(matrix))
        for factor, matrix in word
    )


def word_key(word):
    return tuple((factor, bytes(matrix.reshape(-1)))
                 for factor, matrix in word)


def boundary_relators(indices, centrality):
    unique = {}
    words = boundary_words()
    for index in indices:
        collision = words[index]
        if centrality:
            for _name, generator in factor_generators():
                relation = commutator(generator, collision)
                unique.setdefault(word_key(relation), relation)
        else:
            unique.setdefault(word_key(collision), collision)
    return list(unique.values())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--indices", type=int, nargs="*", default=None,
        help="boundary indices to centralize (default: all 234)")
    parser.add_argument(
        "--kill-collisions", action="store_true",
        help="impose q=1 instead of the genuine [s,q]=1 audit")
    parser.add_argument("--skip-size", action="store_true")
    args = parser.parse_args()
    indices = (list(range(len(boundary_words())))
               if args.indices is None else args.indices)
    generators = [word[0][1] for _, word in factor_generators()[:6]]
    print("G:=Group([%s]);;" % ",".join(
        gap_perm(generator) for generator in generators))
    print("iso:=IsomorphismFpGroup(G);; F:=Image(iso);;")
    print("P:=FreeProduct(F,F);;")
    print("e1:=Embedding(P,1);; e2:=Embedding(P,2);;")
    print("i1:=g->Image(e1,Image(iso,g));;")
    print("i2:=g->Image(e2,Image(iso,g));;")
    relators = boundary_relators(indices, not args.kill_collisions)
    print('Print("boundary_indices %s\\n");' % ",".join(map(str, indices)))
    print('Print("relation_mode %s\\n");' % (
        "kill" if args.kill_collisions else "centrality"))
    print('Print("relators %d\\n");' % len(relators))
    print("rels:=[")
    for word in relators:
        print("%s," % embedded_word(word))
    print("];;")
    print("raw:=P/rels;;")
    print("nat:=GroupHomomorphismByImages(P,raw,"
          "GeneratorsOfGroup(P),GeneratorsOfGroup(raw));;")
    print("simp:=IsomorphismSimplifiedFpGroup(raw);;")
    print("Q:=Image(simp);;")
    print('Print("simplified_generators ",Length(GeneratorsOfGroup(Q)),"\\n");')
    print('Print("simplified_relators ",Length(RelatorsOfFpGroup(Q)),"\\n");')

    alignment = matrix_from_key(bytes.fromhex(INNER_ALIGNMENT_HEX))
    alignment_inverse = gf2_inv(alignment)
    bridges = []
    for row, column in ((0, 1), (1, 0), (1, 2), (2, 1)):
        h = I4.copy()
        h[row, column] ^= 1
        aligned = gf2_mul(gf2_mul(alignment, h), alignment_inverse)
        bridges.append(
            "i2(%s)*i1(%s)^-1" % (gap_perm(h), gap_perm(aligned)))
    print("bridges:=[%s];;" % ",".join(bridges))
    print("bridgeImages:=List(bridges,b->Image(simp,Image(nat,b)));;")
    print('Print("bridge_trivial ",List(bridgeImages,IsOne),"\\n");')
    if not args.skip_size:
        print('Print("quotient_size ",Size(Q),"\\n");')
    print("QUIT;")


if __name__ == "__main__":
    main()
