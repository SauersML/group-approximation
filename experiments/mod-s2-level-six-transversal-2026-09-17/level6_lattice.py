#!/usr/bin/env python3
"""Stage 3: H_1(M''), the separating-twist classes, W(Gamma'), block sums over
the ten level-two splittings (= the ten 3-subsets S), a transversal search,
d(Gamma'), and the best l1 certificate, from the output of rs_elim.cpp.

Classes are the distinct reduced vectors (exact: reduction modulo the HNF of
the relators surviving elimination).  For Gamma(6) the class count is checked
against the 900 = 10 * 90 symplectic splittings mod 6, and the label of each
class (S, ordered pair of mod-3 planes) is checked to be constant on classes.

The twist vectors in elim.txt are either all (coset, twist) pairs in c-major
order (no pkl given) or the selection written by level6_dump.py (pkl given;
the selection is recomputed deterministically from the pkl with PER per label).

Usage: python3 level6_lattice.py elim.txt out.json [cosets.pkl [PER]]
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
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-level-eight-transversal-2026-09-17"))
import census as C  # noqa: E402
import level8_purebraid as P  # noqa: E402
from flint import fmpz_mat  # noqa: E402


def read_elim(path):
    with open(path) as fh:
        ncol = int(fh.readline())
        cols = [int(x) for x in fh.readline().split()]
        assert len(cols) == ncol
        pos = {g: i for i, g in enumerate(cols)}

        def rows(n):
            out = []
            for _ in range(n):
                t = fh.readline().split()
                k = int(t[0])
                r = [0] * ncol
                for i in range(k):
                    r[pos[int(t[1 + 2 * i])]] = int(t[2 + 2 * i])
                out.append(tuple(r))
            return out
        R = rows(int(fh.readline()))
        V = rows(int(fh.readline()))
        line = fh.readline()
        D = rows(int(line)) if line.strip() else None
    return ncol, R, V, D


def labels6(objs, sel):
    """Label (S, P3(e1,f1), P3(e2,f2)) of the class rep_c w_S^-1 t_s w_S rep_c^-1,
    in both conventions (planes spanned by columns / rows of M), per pair."""
    from level6_cosets import span3
    winv = {S: P.sigma_matrix(P.binv(P.CONJ[S])) for S in P.TRIPLES}
    out = {"columns": [], "rows": []}
    for c, t in sel:
        A = np.array(objs[c], dtype=np.int64).reshape(4, 4)
        if True:
            S = P.TRIPLES[t]
            M = (A @ winv[S]) % 3
            X = M.T
            out["columns"].append((S, span3([X[0], X[1]]), span3([X[2], X[3]])))
            out["rows"].append((S, span3([M[0], M[1]]), span3([M[2], M[3]])))
    return out


def transversal_milp(B, block, m):
    """0/1 vector in the row lattice of B (a Z-basis of W) with one 1 per block."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(B, dtype=float)
    r = Bf.shape[0]
    # variables: y (r integers), x (m binaries);  x = y B
    A_eq = np.hstack([Bf.T, -np.eye(m)])
    Blk = np.zeros((10, r + m))
    for j in range(m):
        Blk[block[j], r + j] = 1
    cons = [LinearConstraint(A_eq, 0, 0), LinearConstraint(Blk, 1, 1)]
    integ = np.ones(r + m)
    lb = np.concatenate([np.full(r, -1e6), np.zeros(m)])
    ub = np.concatenate([np.full(r, 1e6), np.ones(m)])
    res = milp(np.zeros(r + m), constraints=cons, integrality=integ,
               bounds=Bounds(lb, ub), options={"time_limit": 3600})
    if res.x is None:
        return None, res.status
    y = [int(round(v)) for v in res.x[:r]]
    w = [sum(B[i][j] * y[i] for i in range(r)) for j in range(m)]
    assert all(a in (0, 1) for a in w)
    assert all(sum(w[j] for j in range(m) if block[j] == b) == 1 for b in range(10))
    return w, res.status


def main(elim, out, pkl=None, per=2):
    t0 = time.time()
    n, R, V, Dres = read_elim(elim)
    if pkl:
        sys.path.insert(0, HERE)
        import level6_dump as D
        objs = pickle.load(open(pkl, "rb"))["objs"]
        sel = D.selection(objs, int(per))
    else:
        sel = [(c, t) for c in range(len(V) // 10) for t in range(10)]
    assert len(sel) == len(V), (len(sel), len(V))
    R = sorted(set(r for r in R if any(r)))
    H = C.hnf_rows([list(r) for r in R], n) if R else []
    rank, tors = C.h1_invariants(H, n)
    print(f"H_1(M'') = Z^{rank} + torsion {tors}; live relators {len(R)} "
          f"[{time.time()-t0:.1f}s]", flush=True)
    if Dres is not None:
        # rows discarded by the selection, pushed through the same pivots:
        # each must lie in the span of the live relators, so L0 = L exactly
        bad = sum(1 for r in Dres if any(C.reduce_mod_hnf(r, H)))
        print(f"verification: {len(Dres)} residues, outside span {bad}",
              flush=True)
        assert bad == 0
    if H:
        red = {}
        Vr = []
        for v in V:
            if v not in red:
                red[v] = C.reduce_mod_hnf(v, H)
            Vr.append(red[v])
    else:
        Vr = V
    keys = sorted(set(Vr))
    kid = {k: i for i, k in enumerate(keys)}
    vclass = [kid[v] for v in Vr]
    m = len(keys)
    S_of = [P.TRIPLES[t] for c, t in sel]
    block = [None] * m
    for t, c in enumerate(vclass):
        b = P.TRIPLES.index(S_of[t])
        assert block[c] in (None, b), "class over two level-two splittings"
        block[c] = b
    per_split = [block.count(i) for i in range(10)]
    res = {"cosets": 1 + max(c for c, t in sel), "twist_vectors": len(V), "h1_rank": rank, "h1_torsion": tors,
           "live_relators": len(R), "classes": m,
           "verified_residues": None if Dres is None else len(Dres),
           "classes_per_splitting": per_split}
    print(f"classes {m}, per splitting {per_split}", flush=True)
    if pkl:
        L = labels6(objs, sel)
        for conv, lab in L.items():
            cl = {}
            ok = True
            for t, c in enumerate(vclass):
                if cl.setdefault(c, lab[t]) != lab[t]:
                    ok = False
                    break
            inj = ok and len(set(cl.values())) == m
            print(f"label convention {conv}: constant on classes {ok}, "
                  f"injective {inj}", flush=True)
            res[f"label_{conv}_constant"] = ok
            res[f"label_{conv}_injective"] = inj
    B = C.w_lattice(H, [list(k) for k in keys], n)
    snf = fmpz_mat(B).snf()
    diag = [abs(int(snf[i, i])) for i in range(min(snf.nrows(), snf.ncols()))]
    g = 0
    for row in B:
        g = gcd(g, sum(row))
    bs_ok = all(len({sum(row[j] for j in range(m) if block[j] == i)
                     for i in range(10)}) == 1 for row in B)
    res.update({"W_rank": len(B), "W_basis_snf_nonunit":
                [x for x in diag if x != 1], "gcd_aug": g,
                "block_sum_identity_on_basis": bs_ok})
    print(f"W rank {len(B)}; SNF nonunit {res['W_basis_snf_nonunit']}; gcd aug"
          f" {g}; block sums equal {bs_ok} [{time.time()-t0:.1f}s]", flush=True)
    pickle.dump({"B": B, "block": block, "keys": keys, "vclass": vclass},
                open(out + ".pkl", "wb"))
    w, st = transversal_milp(B, block, m)
    res["transversal"] = None if w is None else [j for j, a in enumerate(w) if a]
    res["transversal_milp_status"] = int(st)
    print("transversal:", res["transversal"], "status", st,
          f"[{time.time()-t0:.1f}s]", flush=True)
    json.dump(res, open(out, "w"), indent=1)
    dist = C.distance_milp(B)
    if dist is not None:
        res["d"] = str(dist[0])
        res["theta_values"] = sorted(set(str(x) for x in dist[1]))
        print("d =", dist[0], "theta", res["theta_values"], flush=True)
    json.dump(res, open(out, "w"), indent=1)
    l1, w = C.best_certificate(B)
    res["cert_l1"], res["cert_aug"] = l1, (sum(w) if w else None)
    print("best certificate l1", l1, "aug", res["cert_aug"],
          f"[{time.time()-t0:.1f}s]", flush=True)
    json.dump(res, open(out, "w"), indent=1)


if __name__ == "__main__":
    main(*sys.argv[1:])
