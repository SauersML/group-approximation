#!/usr/bin/env python3
"""Third stage: structure of W(Gamma(4)).

* maps each of the 160 classes to its mod-2 homology splitting (10 of them),
* counts the transversal 0/1 relations (one class above each splitting,
  sum = 0 in H_1(M_4)) by meet in the middle,
* checks whether these lifted level-two relations generate W over Z.
"""
import json
import os
import pickle
import random
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
from flint import fmpz_mat  # noqa: E402
from gamma4_lattice import incremental_hnf  # noqa: E402

J2 = np.array([[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]])


def perp_mod2(P):
    """Symplectic complement of the row space P (2 x 4) in F_2^4."""
    vs = [np.array(v) for v in np.ndindex(2, 2, 2, 2)]
    good = [v for v in vs if all((np.array(p) @ J2 @ v) % 2 == 0 for p in P)]
    return C.rref_mod_p(np.array(good), 2)


def splitting_key(A, conv):
    A = np.array(A).reshape(4, 4) % 2
    M = A if conv == 0 else A.T
    P = C.rref_mod_p((M @ np.array([[1, 0], [0, 1], [0, 0], [0, 0]])).T, 2) \
        if conv in (0, 1) else None
    return frozenset([P, perp_mod2(P)])


def load(pkl):
    d = pickle.load(open(pkl, "rb"))
    cols = d["cols"]
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(d["R"], cols)})
    H = incremental_hnf([list(r) for r in Rd], n)
    Vd = C.to_dense(d["V"], cols)
    red = [C.reduce_mod_hnf(v, H) for v in Vd]
    classes = sorted(set(red))
    cidx = {k: i for i, k in enumerate(classes)}
    key_class = [cidx[r] for r in red]
    coset_class = [key_class[k] for k in d["coset_key"]]
    return n, H, classes, coset_class, d["objs"]


def class_splittings(coset_class, objs, nclass):
    out = {}
    for conv in (0, 1):
        sp = [set() for _ in range(nclass)]
        for c, A in enumerate(objs):
            sp[coset_class[c]].add(splitting_key(A, conv))
        if all(len(s) == 1 for s in sp):
            labels = sorted({next(iter(s)) for s in sp}, key=str)
            lab = {s: i for i, s in enumerate(labels)}
            out[conv] = [lab[next(iter(s))] for s in sp]
    return out


def phi_matrix(H, n):
    """Integer matrix K with ker(K) = Q-span(H) (so = rowspace H, saturated)."""
    Kf, nul = fmpz_mat(H).nullspace()
    return np.array([[int(Kf[i, j]) for i in range(n)] for j in range(nul)],
                    dtype=np.int64)


def half_sums(groups):
    """All sums choosing one vector from each group; returns (sums, choices)."""
    sums = np.zeros((1, groups[0].shape[1]), dtype=np.int64)
    choice = np.zeros((1, 0), dtype=np.int64)
    for G in groups:
        k = G.shape[0]
        sums = (sums[:, None, :] + G[None, :, :]).reshape(-1, G.shape[1])
        choice = np.hstack([np.repeat(choice, k, axis=0),
                            np.tile(np.arange(k), len(choice))[:, None]])
    return sums, choice


def main(pkl, out):
    t0 = time.time()
    n, H, classes, coset_class, objs = load(pkl)
    m = len(classes)
    sp = class_splittings(coset_class, objs, m)
    print("well-defined splitting conventions:", list(sp), flush=True)
    lab = sp[min(sp)]
    over = [[c for c in range(m) if lab[c] == s] for s in range(10)]
    print("classes over each splitting:", [len(o) for o in over], flush=True)
    K = phi_matrix(H, n)
    Phi = np.array([K @ np.array(v, dtype=np.int64) for v in classes])
    res = {"classes_over_splitting": [len(o) for o in over],
           "h1_rank": int(K.shape[0])}
    # relations supported over a single splitting (augmentation-free part)
    loc = [int(np.linalg.matrix_rank(Phi[o].astype(float))) for o in over]
    res["rank_of_classes_over_each_splitting"] = loc
    print("rank of the 16 classes over each splitting:", loc, flush=True)
    groups = [Phi[o] for o in over]
    Ls, Lc = half_sums(groups[:5])
    Rs, Rc = half_sums(groups[5:])
    table = {}
    for i, row in enumerate(Ls):
        table.setdefault(row.tobytes(), []).append(i)
    count, sols = 0, []
    for j, row in enumerate(-Rs):
        hit = table.get(row.tobytes())
        if hit:
            count += len(hit)
            for i in hit:
                if len(sols) < 20000:
                    sols.append(list(Lc[i]) + list(Rc[j]))
    res["transversal_relations"] = count
    print(f"transversal 0/1 relations: {count} of 16^10  "
          f"[{time.time()-t0:.1f}s]", flush=True)
    B = C.w_lattice(H, [list(k) for k in classes], n)
    random.seed(1)
    random.shuffle(sols)
    vecs = []
    for s in sols[:4000]:
        w = [0] * m
        for g, ch in enumerate(s):
            w[over[g][ch]] += 1
        vecs.append(w)
    Hs = C.hnf_rows(vecs, m) if vecs else []
    HB = C.hnf_rows(B, m)
    res["W_rank"] = len(HB)
    res["span_rank_of_transversal"] = len(Hs)
    res["transversal_generate_W"] = (Hs == HB)
    if Hs and len(Hs) == len(HB):
        D = fmpz_mat(Hs).snf()
        DB = fmpz_mat(HB).snf()
        pr = lambda X: [abs(int(X[i, i])) for i in range(X.nrows())]
        res["index_in_W_snf"] = [a for a in pr(D) if a != 1]
        res["W_snf"] = [a for a in pr(DB) if a != 1]
    print({k: res[k] for k in res if k.startswith(("span", "trans", "W", "ind"))},
          flush=True)
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
