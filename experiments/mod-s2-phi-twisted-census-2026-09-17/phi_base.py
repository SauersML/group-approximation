#!/usr/bin/env python3
"""Integral census of M_Phi in the coordinates of twisted.py (t = 1), saving
the class of every twist row (base coset c, triple k) and a basis of W(Phi).
Must reproduce the three-Sylow census: H_1 = Z^30 + (Z/3)^8, 180 classes,
rank W = 150, d = 1/30.

Usage: python3 phi_base.py [out.json]
"""
import json
import os
import sys

import twisted as T
import sylow as S
import fastelim

HERE = os.path.dirname(os.path.abspath(__file__))


def main(outp):
    ngen, R, Z, zinfo, info = T.build(0, trivial=True)
    rows = [{g: sum(a) for g, a in r.items() if sum(a)} for r in R]
    vs = [{g: sum(a) for g, a in z.items() if sum(a)} for z in Z]
    out, (cols, H, keys, cls_of, B) = S.lattice_from_rs(
        ngen, rows, vs, "phi-base", info["base_cosets"],
        elim=fastelim.eliminate)
    out.update(info)
    out["cls_of"] = cls_of
    out["W_basis"] = [list(map(int, b)) for b in B]
    json.dump(out, open(outp, "w"))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else
         os.path.join(HERE, "phi-base.json"))
