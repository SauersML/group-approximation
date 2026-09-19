#!/usr/bin/env python3
"""Second stage for level8_index2.py output: H_1(M''), the distinct
separating-twist classes, their level-two splittings, W(Gamma''), the block
sums of a W basis over the 10 level-two splittings, d(Gamma''), the best l1
certificate, and the positive-relation mass A_+ (is there w >= 0 in W with
aug(w) = 10, i.e. a transversal relation?).

Usage: python3 level8_lattice.py reduced.pkl out.json
"""
import json
import os
import pickle
import sys
import time
from math import gcd

import numpy as np

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


def plane_key(cols4):
    """Canonical key of the F_2-span of the given column vectors."""
    rows = [tuple(int(x) % 2 for x in v) for v in cols4]
    span = set()
    for a in (0, 1):
        for b in (0, 1):
            span.add(tuple((a * x + b * y) % 2 for x, y in zip(*rows)))
    return tuple(sorted(span))


def splitting_label(key, use_rows):
    A = np.array(key[0], dtype=np.int64).reshape(4, 4) % 2
    M = A if use_rows else A.T
    # use_rows: planes spanned by rows 0,1 / 2,3; else columns 0,1 / 2,3
    p = plane_key([M[0], M[1]])
    q = plane_key([M[2], M[3]])
    return tuple(sorted((p, q)))


def positive_mass(B, target):
    """Is there w = y B >= 0 with aug(w) = target?  Returns w or None."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(B, dtype=float)
    r, m = Bf.shape
    aug = Bf.sum(axis=1)
    cons = [LinearConstraint(aug[None, :], target, target),
            LinearConstraint(Bf.T, 0, np.inf)]
    res = milp(np.zeros(r), constraints=cons, integrality=np.ones(r),
               bounds=Bounds(np.full(r, -1e6), np.full(r, 1e6)),
               options={"time_limit": 1800})
    if res.x is None:
        return None if res.status in (2,) else "undecided"
    y = [int(round(v)) for v in res.x]
    w = [sum(B[i][j] * y[i] for i in range(r)) for j in range(m)]
    assert min(w) >= 0 and sum(w) == target
    return w


def main(pkl, out):
    t0 = time.time()
    d = pickle.load(open(pkl, "rb"))
    cols, R, V, mult = d["cols"], d["R"], d["V"], d["mult"]
    objs, coset_key = d["objs"], d["coset_key"]
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(R, cols)})
    H = incremental_hnf([list(r) for r in Rd], n)
    rank, tors = C.h1_invariants(H, n)
    print(f"H_1(M'') = Z^{rank} + torsion {tors} [{time.time()-t0:.1f}s]",
          flush=True)
    Vd = C.to_dense(V, cols)
    red = [C.reduce_mod_hnf(v, H) for v in Vd]
    keys = sorted(set(red))
    kid = {k: i for i, k in enumerate(keys)}
    vclass = [kid[k] for k in red]                 # reduced-v index -> class
    m = len(keys)
    # level-two splitting of each class (both conventions, keep the one that
    # is constant on classes)
    label = None
    for use_rows in (False, True):
        lab = {}
        ok = True
        for c, key in enumerate(objs):
            cl = vclass[coset_key[c]]
            s = splitting_label(key, use_rows)
            if lab.setdefault(cl, s) != s:
                ok = False
                break
        if ok and len(set(lab.values())) == 10:
            label, conv = lab, ("rows" if use_rows else "columns")
            break
    assert label is not None, "no consistent level-two labelling"
    splits = sorted(set(label.values()))
    sid = {s: i for i, s in enumerate(splits)}
    block = [sid[label[c]] for c in range(m)]
    per_split = [block.count(i) for i in range(10)]
    counts = {}
    for c, key in enumerate(objs):
        cl = vclass[coset_key[c]]
        counts[cl] = counts.get(cl, 0) + 1
    print(f"classes {m}, per splitting {per_split}, convention {conv}, "
          f"coset counts {sorted(set(counts.values()))}", flush=True)
    H2 = C.hnf_rows(H + [list(k) for k in keys], n)
    q_rank, q_tors = C.h1_invariants(H2, n)
    B = C.w_lattice(H, [list(k) for k in keys], n)
    Bm = fmpz_mat(B)
    snf = Bm.snf()
    diag = [abs(int(snf[i, i])) for i in range(min(snf.nrows(), snf.ncols()))]
    g = 0
    for row in B:
        g = gcd(g, sum(row))
    bs_ok = all(len({sum(row[j] for j in range(m) if block[j] == i)
                     for i in range(10)}) == 1 and
                sum(row) == 10 * sum(row[j] for j in range(m) if block[j] == 0)
                for row in B)
    print(f"W rank {len(B)} in Z^{m}; SNF nonunit {[x for x in diag if x != 1]}"
          f"; gcd aug {g}; block-sum identity on basis {bs_ok} "
          f"[{time.time()-t0:.1f}s]", flush=True)
    res = {"f": d.get("f"), "cosets": len(objs), "h1_rank": rank,
           "h1_torsion": tors, "h1_Gamma2prime_torsion": q_tors,
           "h1_Gamma2prime_rank": q_rank, "classes": m,
           "classes_per_splitting": per_split, "label_convention": conv,
           "class_coset_counts": sorted(set(counts.values())),
           "W_rank": len(B), "W_basis_snf_nonunit": [x for x in diag if x != 1],
           "gcd_aug": g, "block_sum_identity_on_basis": bs_ok}
    w10 = positive_mass(B, 10)
    res["positive_aug10"] = (w10 if isinstance(w10, str) else
                             (None if w10 is None else
                              [j for j, a in enumerate(w10) if a]))
    print("positive relation of augmentation 10:", res["positive_aug10"],
          flush=True)
    if w10 is None:
        w20 = positive_mass(B, 20)
        res["positive_aug20_support"] = (w20 if isinstance(w20, str) else
                                         (None if w20 is None else
                                          sum(1 for a in w20 if a)))
        print("positive relation of augmentation 20:",
              res["positive_aug20_support"], flush=True)
    dist = C.distance_milp(B)
    if dist is not None:
        res["d"] = str(dist[0])
        res["theta_values"] = sorted(set(dist[1]))
        print("d =", dist[0], "theta values", res["theta_values"], flush=True)
    l1, w = C.best_certificate(B)
    res["cert_l1"], res["cert_aug"] = l1, (sum(w) if w else None)
    print("best certificate l1", l1, "aug", res["cert_aug"], flush=True)
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out, f"[{time.time()-t0:.1f}s]")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
