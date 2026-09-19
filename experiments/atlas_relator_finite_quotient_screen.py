"""Finite-quotient screens for candidate relator lists on the two-chart atlas.

A candidate finite list T of words in Rbar = ker(A8 * A8 -> Q) is usable in the
canonical regular-A8 criterion only if Nbar = [Pbar, Rbar] <= <<T>>.  In that
case Pbar/<<T>> is a quotient of U_Q, which is quasisimple over the infinite
simple group Q and therefore has NO nontrivial finite quotient.  So every
homomorphism from Pbar onto a nontrivial finite group that kills all of T
refutes usability of T.

Two families of such homomorphisms are screened here.

  (D) The direct-product retraction (p1, p2) : A8 * A8 ->> A8 x A8, which
      deletes the letters of the other factor.  Covers exactly the maps whose
      restriction to one free factor is trivial (A8 is simple, so a factor
      restriction is trivial or injective).

  (F) The automorphism folds phi_{g,theta}(x) = x on factor one and
      g theta(x) g^{-1} on factor two, for g in A8 and theta in {id, graph}.
      These are the 40320 maps onto A8 whose two factor restrictions are both
      injective with equal image.

This script also reports exact X-word lengths.  In a free product the word
length with respect to the union of the two factor generating sets is additive
over free-product syllables, so the X-length of a reduced word is the sum of
the six-transvection word lengths of its GL_4(F2) syllables.
"""

import argparse
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from atlas_kernel_collision_enumerator import (  # noqa: E402
    enumerate_ball,
    factor_projections,
    spanning_tree_kernel_words,
)
from atlas_two_chart_search import I4, gf2_inv, gf2_mul, transvection  # noqa: E402

TRANSVECTIONS = [transvection(r, c) for r, c in
                 ((0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2))]


def transvection_word_lengths():
    """Word length in GL_4(F2) with respect to the six adjacent transvections."""
    identity = np.eye(4, dtype=np.uint8)
    lengths = {identity.tobytes(): 0}
    elements = {identity.tobytes(): identity}
    frontier = [identity]
    depth = 0
    while frontier:
        depth += 1
        nxt = []
        for g in frontier:
            for s in TRANSVECTIONS:
                h = gf2_mul(g, s)
                key = h.tobytes()
                if key not in lengths:
                    lengths[key] = depth
                    elements[key] = h
                    nxt.append(h)
        frontier = nxt
    return lengths, elements


def x_length(word, lengths):
    return sum(lengths[matrix.tobytes()] for _factor, matrix in word)


def graph_automorphism(matrix):
    """theta(g) = (g^{-1})^T, the outer automorphism of GL_4(F2) = A8."""
    return gf2_inv(matrix).T.copy()


def fold_image(word, conjugator, twist):
    value = I4.copy()
    for factor, matrix in word:
        if factor == 1:
            letter = matrix
        else:
            twisted = graph_automorphism(matrix) if twist else matrix
            letter = gf2_mul(gf2_mul(conjugator, twisted), gf2_inv(conjugator))
        value = gf2_mul(value, letter)
    return value


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--radius", type=int, default=2)
    parser.add_argument("--fold-screen", action="store_true",
                        help="scan all 40320 automorphism folds onto A8")
    args = parser.parse_args()

    lengths, elements = transvection_word_lengths()
    print("GL_4(F2) transvection-length profile: max =",
          max(lengths.values()), " elements =", len(lengths))

    states, _sizes = enumerate_ball(args.radius)
    kernel_words, _collisions, _depths = spanning_tree_kernel_words(states)
    print("radius %d: %d spanning-tree kernel generators"
          % (args.radius, len(kernel_words)))

    if kernel_words:
        all_x = [x_length(w, lengths) for w in kernel_words]
        print("  X-length of tree generators: min %d, max %d"
              % (min(all_x), max(all_x)))

    boundary = []
    for word in kernel_words:
        p1, p2 = factor_projections(word)
        if not (np.array_equal(p1, I4) and np.array_equal(p2, I4)):
            boundary.append(word)
    print("  words with nontrivial (p1,p2): %d of %d"
          % (len(boundary), len(kernel_words)))
    if boundary:
        bx = [x_length(w, lengths) for w in boundary]
        print("  X-length on that boundary: min %d, max %d"
              % (min(bx), max(bx)))
        print("  SCREEN (D): passed -- A8 x A8 is not a quotient")
    else:
        print("  SCREEN (D): FAILED -- (p1,p2) kills the whole window, so")
        print("              <<window>> does not contain Nbar")

    if args.fold_screen and kernel_words:
        survivors = []
        for twist in (False, True):
            for conjugator in elements.values():
                ok = True
                for word in kernel_words:
                    if not np.array_equal(
                            fold_image(word, conjugator, twist), I4):
                        ok = False
                        break
                if ok:
                    survivors.append((twist, conjugator.tolist()))
        print("  SCREEN (F): %d of 40320 automorphism folds kill the whole "
              "window" % len(survivors))
        if survivors:
            print("              FAILED -- example", survivors[0])
        else:
            print("              passed -- no fold onto A8 survives")


if __name__ == "__main__":
    main()
