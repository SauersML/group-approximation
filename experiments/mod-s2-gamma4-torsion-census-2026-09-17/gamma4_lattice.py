#!/usr/bin/env python3
"""Second stage: from the unit-eliminated presentation of H_1(K4) (gamma4.py
output) compute H_1(M_4), the distinct separating-twist classes, the relation
lattice W(Gamma(4)) including torsion, d(Gamma(4)) and an l1 certificate."""
import json
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
from flint import fmpz_mat  # noqa: E402


def incremental_hnf(rows, ncols, chunk=3000):
    H = []
    for k in range(0, len(rows), chunk):
        H = C.hnf_rows(H + rows[k:k + chunk], ncols)
    return H


def main(pkl, out):
    t0 = time.time()
    d = pickle.load(open(pkl, "rb"))
    cols, R, V, mult = d["cols"], d["R"], d["V"], d["mult"]
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(R, cols)})
    H = incremental_hnf([list(r) for r in Rd], n)
    rank, tors = C.h1_invariants(H, n)
    print(f"H_1(M_4) = Z^{rank} + torsion {tors}  [{time.time()-t0:.1f}s]",
          flush=True)
    Vd = C.to_dense(V, cols)
    classes = {}
    for v, m in zip(Vd, mult):
        key = C.reduce_mod_hnf(v, H)
        classes[key] = classes.get(key, 0) + m
    keys = sorted(classes)
    print(f"distinct separating classes: {len(keys)}; coset counts "
          f"{sorted(set(classes.values()))}", flush=True)
    B = C.w_lattice(H, [list(k) for k in keys], n)
    m = len(keys)
    Bm = fmpz_mat(B) if B else None
    snf = Bm.snf() if B else None
    diag = [abs(int(snf[i, i])) for i in range(min(snf.nrows(), snf.ncols()))]
    augs = [sum(r) for r in B]
    g = 0
    for a in augs:
        from math import gcd
        g = gcd(g, a)
    print(f"W: rank {len(B)} in Z^{m}; SNF of W-basis nonunit diag "
          f"{[x for x in diag if x != 1]}; gcd aug {g}", flush=True)
    res = {"cosets": 61440, "h1_rank": rank, "h1_torsion": tors,
           "classes": m, "class_coset_counts": sorted(set(classes.values())),
           "W_rank": len(B), "W_basis_snf_nonunit": [x for x in diag if x != 1],
           "gcd_aug": g}
    dist = C.distance_milp(B)
    if dist is not None:
        res["d"] = str(dist[0])
        res["theta_values"] = sorted(set(dist[1]))
        print("d(Gamma(4)) =", dist[0], "theta values", res["theta_values"],
              flush=True)
    l1, w = C.best_certificate(B)
    res["cert_l1"], res["cert_aug"] = l1, (sum(w) if w else None)
    res["cert_support"] = sum(1 for a in w if a) if w else None
    print("best certificate l1", l1, "aug", res["cert_aug"], flush=True)
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out, f"[{time.time()-t0:.1f}s]")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
