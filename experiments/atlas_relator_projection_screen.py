"""Finite-quotient screen for candidate atlas relator lists.

Background.  Write

    Pbar = K1 * K2 = A8 * A8  --rho-->  Q = L_F2(1,2)^times,
    Rbar = ker rho,   Nbar = [Pbar, Rbar],   U_Q = Pbar/Nbar.

A candidate finite list T of kernel words is *usable* in the canonical
regular-A8 criterion only if Nbar <= <<T>>_Pbar.  Equivalently Pbar/<<T>> must
be a quotient of U_Q.  U_Q is quasisimple over the infinite simple group Q, so
it has no nontrivial finite quotient at all.  Therefore:

    if some homomorphism phi : Pbar -> F onto a nontrivial FINITE group kills
    every word of T, then <<T>> does not contain Nbar, and T is unusable.

The cheapest such phi is the canonical retraction onto the direct product,

    (p1, p2) : A8 * A8 --->> A8 x A8,

where p_i deletes every letter from the other free factor.  This script
evaluates (p1, p2) on the complete spanning-tree kernel windows produced by
`atlas_kernel_collision_enumerator` and reports the verdict per radius.

Everything here is exact GF(2) / exact Leavitt prefix arithmetic; no
floating point is used.
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
from atlas_two_chart_search import I4  # noqa: E402


def word_length(word):
    """Number of X-letters, each letter being one adjacent transvection."""
    return len(word)


def screen(radius, verbose=False):
    states, _level_sizes = enumerate_ball(radius)
    kernel_words, collision_sizes, _depths = spanning_tree_kernel_words(states)

    trivial = 0
    nontrivial = []
    for word in kernel_words:
        p1, p2 = factor_projections(word)
        if np.array_equal(p1, I4) and np.array_equal(p2, I4):
            trivial += 1
        else:
            nontrivial.append((word_length(word), word, p1, p2))

    report = {
        "radius": radius,
        "complete_kernel_word_radius": 2 * radius,
        "ball": len(states),
        "collision_buckets": len(collision_sizes),
        "tree_kernel_generators": len(kernel_words),
        "trivial_projection_pair": trivial,
        "nontrivial_projection_pair": len(nontrivial),
    }
    if nontrivial:
        report["min_length_with_nontrivial_projection"] = min(
            item[0] for item in nontrivial)
    if kernel_words:
        report["max_tree_word_length"] = max(
            word_length(w) for w in kernel_words)
    if verbose and nontrivial:
        report["sample"] = [
            (item[0], item[2].tolist(), item[3].tolist())
            for item in nontrivial[:5]
        ]
    return report


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-radius", type=int, default=4)
    parser.add_argument("--min-radius", type=int, default=1)
    parser.add_argument("--verbose", action="store_true")
    args = parser.parse_args()

    print("radius | 2r | tree gens | trivial (p1,p2) | nontrivial | verdict")
    for radius in range(args.min_radius, args.max_radius + 1):
        report = screen(radius, verbose=args.verbose)
        killed = report["nontrivial_projection_pair"] == 0
        verdict = ("A8xA8 SURVIVES -> window provably incomplete"
                   if killed else "A8xA8 killed -> screen passed")
        print("%6d | %2d | %9d | %15d | %10d | %s" % (
            report["radius"],
            report["complete_kernel_word_radius"],
            report["tree_kernel_generators"],
            report["trivial_projection_pair"],
            report["nontrivial_projection_pair"],
            verdict,
        ))
        if args.verbose:
            print("        detail:", report)


if __name__ == "__main__":
    main()
