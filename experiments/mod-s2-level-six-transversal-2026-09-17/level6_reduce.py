#!/usr/bin/env python3
"""Stage 2 for Gamma(6): abelianised Reidemeister-Schreier over Artin's
presentation of K2 = PMod(S_{0,6}) on the 25920 cosets of stage 1, exact
unit elimination, and the reduced separating-twist vectors.

Identical in method to level8_purebraid.reduce_mode (validated there against
the Gamma(2) and Gamma(4) nodes); only the coset space differs.

Usage: python3 level6_reduce.py cosets.pkl out.pkl
"""
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
L8DIR = os.path.join(HERE, "..", "mod-s2-level-eight-transversal-2026-09-17")
sys.path.insert(0, L8DIR)
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import level8_purebraid as P  # noqa: E402


def main(inp, out):
    t0 = time.time()
    d = pickle.load(open(inp, "rb"))
    act, inv, rels, split = d["act"], d["inv"], d["rels"], d["split"]
    k = len(act)
    gen = P.schreier(act)
    R = []
    for lhs, rhs in rels:
        for c in range(k):
            vec = {}
            e1 = P.trace(act, inv, gen, c, lhs, vec, 1)
            e2 = P.trace(act, inv, gen, c, rhs, vec, -1)
            assert e1 == e2
            vec = {x: y for x, y in vec.items() if y}
            if vec:
                R.append(vec)
    tS = {S: P.twist3(S) * 2 for S in P.TRIPLES}
    V, lab = [], []
    n = 0
    for c in range(k):
        for S in P.TRIPLES:
            vec = {}
            assert P.trace(act, inv, gen, c, tS[S], vec) == c
            V.append({x: y for x, y in vec.items() if y})
            assert split[n][0] == S
            lab.append(split[n])
            n += 1
    print(f"cosets {k}, Schreier gens {len(gen)}, relators {len(R)}, "
          f"twist vectors {len(V)} [{time.time()-t0:.1f}s]", flush=True)
    del d
    cols, R2, V2 = C.unit_eliminate(len(gen), R, V)
    print(f"after unit elimination: {len(cols)} gens, {len(R2)} relators "
          f"[{time.time()-t0:.1f}s]", flush=True)
    with open(out, "wb") as fh:
        pickle.dump({"cols": cols, "R": R2, "V": V2, "lab": lab,
                     "cosets": k, "schreier_gens": len(gen),
                     "relators": len(R)}, fh)
    print("saved", out, f"[{time.time()-t0:.1f}s]", flush=True)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
