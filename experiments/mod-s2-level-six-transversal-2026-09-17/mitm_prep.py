#!/usr/bin/env python3
"""Write the input of mitm.cpp for one prime p from the level6_modp pickle.

Keeps a set of coordinates that is independent on the row span of Phi_p (the
900 class images), so the zero-sum test on them is equivalent to the full one:
a vector u in the row span that vanishes on these coordinates is 0, because
the restriction to them is injective on the span (rank is preserved).

Usage: python3 mitm_prep.py phi.pkl p out.txt
"""
import pickle
import sys

from flint import nmod_mat


def main(pkl, p, out):
    p = int(p)
    d = pickle.load(open(pkl, "rb"))
    F, block = d["Phi"][p], d["block"]
    m, r = len(F), len(F[0])
    full = nmod_mat([list(x) for x in F], p).rank()
    keep, rk = [], 0
    for k in range(r):
        trial = keep + [k]
        rr = nmod_mat([[F[c][j] for j in trial] for c in range(m)], p).rank()
        if rr > rk:
            keep, rk = trial, rr
    assert rk == full == len(keep)
    with open(out, "w") as f:
        f.write(f"{p} {m} {len(keep)}\n")
        f.write(" ".join(str(b) for b in block) + "\n")
        for c in range(m):
            f.write(" ".join(str(F[c][j] % p) for j in keep) + "\n")
    print(f"p={p}: rank {full}, kept {len(keep)} coordinates -> {out}")


if __name__ == "__main__":
    main(*sys.argv[1:])
