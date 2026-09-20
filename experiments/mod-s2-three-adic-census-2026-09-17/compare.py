#!/usr/bin/env python3
"""Push W(G_Y) forward to the 45 level-3 classes and compare with W(Gamma(3)).

The inclusion M_Y -> M_3 sends each twist class to the class of the same
twist, so push-forward (summing the classes above one level-3 splitting)
maps W(G_Y) into W(Gamma(3)).  Prints the rank and the index of the image,
and whether the 27 GQ(2,4) star vectors of Gamma(3) lie in the image.
Usage: python3 compare.py <orbit> ...
"""
import json
import os
import sys

import numpy as np
from flint import fmpz_mat

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import threeadic  # noqa: E402

G3 = os.path.join(HERE, "..", "mod-s2-torelli-scalar-census-2026-09-17",
                  "census-results-frame-3.json")


def split_key(g):
    g = np.array(g) % 3
    def span(a, b):
        return frozenset(tuple(int(t) for t in (x * a + y * b) % 3)
                         for x in range(3) for y in range(3) if x or y)
    return frozenset([span(g[:, 0], g[:, 1]), span(g[:, 2], g[:, 3])])


def lattice_index(sub, full):
    """[full : sub] for sub <= full of equal rank (rows); None if ranks differ."""
    F = fmpz_mat(full).hnf()
    S = fmpz_mat(sub).hnf()
    rf = sum(1 for i in range(F.nrows()) if any(F[i, j] for j in range(F.ncols())))
    rs = sum(1 for i in range(S.nrows()) if any(S[i, j] for j in range(S.ncols())))
    if rf != rs:
        return None, rf, rs
    # express sub in coordinates of full: solve over Q via stacked SNF
    Fr = [[int(F[i, j]) for j in range(F.ncols())] for i in range(rf)]
    Sr = [[int(S[i, j]) for j in range(S.ncols())] for i in range(rs)]
    import sympy
    A = sympy.Matrix(Fr).T
    coords = [list(A.solve_least_squares(sympy.Matrix(r))) for r in Sr]
    assert all(v.q == 1 for row in coords for v in row)
    C = fmpz_mat([[int(v) for v in row] for row in coords])
    D = C.snf()
    return [abs(int(D[i, i])) for i in range(rs) if abs(int(D[i, i])) != 1], rf, rs


def main(argv):
    g3 = json.load(open(G3))[0]
    keys3 = [split_key(o) for o in g3["class_rep_objects"]]
    pos3 = {k: i for i, k in enumerate(keys3)}
    assert len(pos3) == 45
    W3 = g3["W_basis"]
    idx, lift = threeadic.section()
    for a in argv:
        fn = os.path.join(HERE, f"equivariant-orbit-{a}.json")
        if not os.path.exists(fn):
            fn = os.path.join(HERE, f"threeadic-orbit-{a}.json")
        r = json.load(open(fn))
        cls_to_3 = [pos3[split_key(lift[c // 3])] for c in r["class_rep_cosets"]]
        push = []
        for w in r["W_basis"]:
            v = [0] * 45
            for j, x in enumerate(w):
                v[cls_to_3[j]] += x
            push.append(v)
        elem, rf, rs = lattice_index(push, W3)
        print(json.dumps({"orbit": int(a), "classes": r["classes"],
                          "fibre_sizes": sorted(np.bincount(cls_to_3).tolist()),
                          "rank_W3": rf, "rank_push": rs,
                          "push_index_elementary_divisors": elem}))


if __name__ == "__main__":
    main(sys.argv[1:])
