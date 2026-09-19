#!/usr/bin/env python3
"""Does (C) at right-orbit depth <= d0 force (C) at all depths <= d1 in the
class-two tensor models of Gamma_trap + EXTRA_RELS?

For a ring module W = M_2(F_2[x]/p) and random c_u, K = G0-span of the C-parts
of all relator differences plus (C1),(C2) at depth <= d0 (c2scan.py).  We report,
for each depth j <= d1, how many of the (C1),(C2) differences at depth exactly j
are NOT in K, and whether the head's C-part is in K.
Usage: propagate.py P A D0 D1 SEEDS
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "p22-depth-one-class-two-2026-09-17"))
import random  # noqa: E402

import numpy as np  # noqa: E402

import c2scan as C  # noqa: E402
from words import TRAP_RELS, INVOL_RELS, EXTRA_RELS  # noqa: E402


def per_depth(vals, n, depth):
    out = []
    prev = 0
    for j in range(depth + 1):
        d = C.orbit_rel_diffs(vals, n, j)
        out.append(d[prev:])
        prev = len(d)
    return out


def main():
    p, a = int(sys.argv[1], 0), int(sys.argv[2], 0)
    d0, d1, seeds = map(int, sys.argv[3:6])
    mats, v = C.ring_module(p, a)
    n = v.shape[0]
    for s in range(seeds):
        rng = random.Random(s)
        cu = np.array([[rng.randint(0, 1) for _ in range(n)] for _ in range(n)], np.uint8)
        vals = C.build(mats, v, cu)
        d = C.rel_diffs(vals, TRAP_RELS + INVOL_RELS + EXTRA_RELS, n)
        layers = per_depth(vals, n, d1)
        base = d + [x for L in layers[:d0 + 1] for x in L]
        K = C.closure(mats, base, n)
        miss = [sum(1 for x in L if K.red(x)) for L in layers]
        print("seed %d: dimK %d head_survives %s  (C)-differences outside K by depth %s"
              % (s, len(K.piv), bool(K.red(C.toint(vals["h"][1]))), miss), flush=True)


if __name__ == "__main__":
    main()
