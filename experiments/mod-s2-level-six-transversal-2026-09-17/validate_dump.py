#!/usr/bin/env python3
"""Validation input for rs_elim.cpp at Gamma(2) and Gamma(4), using the coset
spaces of level8_purebraid (whose results are the established Gamma(2) and
Gamma(4) nodes: H_1 = Z^9, 10 classes, W = Z(1,...,1); H_1 = Z^54, 160
classes, W of rank 106, d = 1/30).

Usage: python3 validate_dump.py N2|N4 out.txt
"""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-level-eight-transversal-2026-09-17"))
import level6_dump as D  # noqa: E402
import level8_purebraid as P  # noqa: E402


def main(mode, out):
    rels = P.verify_all()
    canon, rep, N = P.level_setup(mode)
    objs, act, inv, reps = P.enumerate_K2(canon, rep, N)
    with open(out, "w") as fh:
        fh.write(f"{len(act)}\n")
        for row in act:
            fh.write(" ".join(map(str, row)) + "\n")
        fh.write(f"{len(rels)}\n")
        for lhs, rhs in rels:
            fh.write(D.word(lhs) + "\n" + D.word(rhs) + "\n")
        fh.write(f"{len(P.TRIPLES)}\n")
        for S in P.TRIPLES:
            fh.write(D.word(P.twist3(S) * 2) + "\n")
    print(mode, "cosets", len(act))


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
