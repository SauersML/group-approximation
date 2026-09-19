#!/usr/bin/env python3
"""Torelli census below Gamma(4): index-two subgroups Gamma(4) > G > Gamma(8).

Gamma(4)/Gamma(8) = {I + 4Y} ~ sp_4(F_2) (F_2^10), and Sp_4(Z) acts on it by
Ad(g mod 2).  Every index-two subgroup of Gamma(4) containing Gamma(8) is
G_chi = ker(chi) for a nonzero functional chi; conjugate subgroups have the
same d.  For one chi in each Sp_4(F_2)-orbit we build the coset action of
H = B_5/<<Delta^2>> on H/K_chi (K_chi = preimage of G_chi, 2 * 61440 cosets),
using the reduction of gamma4.py (Birman--Hilden + capping), and run the same
abelianised Reidemeister--Schreier / W-lattice / MILP / certificate pipeline.

Right cosets K A are keyed by (A mod 4 up to sign, chi(X)), where
X = A L^{-1} normalised to X = I mod 4 and L is the first mod-8 lift met for
the mod-4 class of A.
"""
import json
import os
import pickle
import sys
import time
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
G4 = os.path.join(HERE, "..", "mod-s2-gamma4-torsion-census-2026-09-17")
sys.path.insert(0, G4)
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import gamma4 as G  # noqa: E402
from gamma4_lattice import incremental_hnf  # noqa: E402

J = C.J
I4 = np.eye(4, dtype=np.int64)


def sinv(A, N):
    return (-J @ A.T @ J) % N


def y_of(X):
    """X = I + 4Y mod 8  ->  Y mod 2 as a flat 16-vector."""
    D = (X - I4) % 8
    assert (D % 4 == 0).all()
    return ((D // 4) % 2).flatten()


def gamma48_basis():
    """RREF basis of Gamma(4)/Gamma(8): Y of the fourth powers of all
    transvections T_x^4 = I + 4 x (x^T J), x in F_2^4 (spans sp_4(F_2))."""
    ys = []
    for v in np.ndindex(2, 2, 2, 2):
        x = np.array(v, dtype=np.int64)
        if x.any():
            ys.append(y_of((I4 + 4 * np.outer(x, x @ J)) % 8))
    R = rref2(ys)
    return np.array(R, dtype=np.int64)


def rref2(rows):
    A = [[int(t) % 2 for t in r] for r in rows]
    out, pr = [], 0
    for col in range(len(A[0])):
        r = next((i for i in range(pr, len(A)) if A[i][col]), None)
        if r is None:
            continue
        A[pr], A[r] = A[r], A[pr]
        for i in range(len(A)):
            if i != pr and A[i][col]:
                A[i] = [(a + b) % 2 for a, b in zip(A[i], A[pr])]
        pr += 1
    return A[:pr]


def coords(Y, R, piv):
    c = np.array([Y[p] for p in piv], dtype=np.int64)
    assert ((c @ R) % 2 == Y % 2).all(), "Y not in span"
    return c


def orbit_reps(R):
    piv = [int(np.nonzero(r)[0][0]) for r in R]
    k = len(R)
    g2 = [C.GENMATS[i] % 2 for i in range(5)]  # all of Sp_4(F_2)
    # matrix of Ad(g) on coordinates: row j = coords(g Y_j g^-1)
    ad = []
    for g in g2:
        gi = sinv(g, 2)
        M = np.array([coords((g @ R[j].reshape(4, 4) @ gi % 2).flatten(), R, piv)
                      for j in range(k)])
        ad.append(M)
    # functional chi (row vector c): chi(Y) = c . coords(Y); action c -> Ad^T
    seen, reps = set(), []
    for v in range(1, 2 ** k):
        c = tuple((v >> i) & 1 for i in range(k))
        if c in seen:
            continue
        orb, q = [c], 0
        seen.add(c)
        while q < len(orb):
            x = np.array(orb[q])
            for M in ad:
                y = tuple(int(t) for t in (M @ x) % 2)
                if y not in seen:
                    seen.add(y)
                    orb.append(y)
            q += 1
        reps.append((c, len(orb)))
    return piv, reps


def enumerate_chi(R, piv, chi, limit=400000):
    mats = [C.GENMATS[i] % 8 for i in range(G.NG)]
    chi = np.array(chi, dtype=np.int64)
    lift = {}

    def key(A):
        k4 = G.canon_pm(A % 4, 4)
        L = lift.get(k4)
        if L is None:
            lift[k4] = A.copy()
            return (k4, 0)
        X = (A @ sinv(L, 8)) % 8
        if not ((X - I4) % 4 == 0).all():
            X = (-X) % 8
        return (k4, int(chi @ coords(y_of(X), R, piv)) % 2)

    start = key(I4.copy())
    index, reps, act = {start: 0}, [I4.copy()], []
    q = 0
    while q < len(reps):
        A = reps[q]
        row = []
        for B in mats:
            nA = (A @ B) % 8
            k = key(nA)
            if k not in index:
                index[k] = len(reps)
                reps.append(nA)
                if len(reps) > limit:
                    raise RuntimeError("orbit exceeds limit")
            row.append(index[k])
        act.append(row)
        q += 1
    objs = [tuple(int(t) for t in (A % 4).flatten()) for A in reps]
    return objs, act


def lean_eliminate(ngen, rels, vs):
    """Same output contract as census.unit_eliminate (surviving columns,
    relators over them, target vectors over them), with less memory:
    pivots only on relators of current length <= L (L raised when stuck),
    and the target vectors are not carried along but rewritten afterwards
    by the recorded substitutions, applied in elimination order.
    Every step is a unimodular change of generators, so Z^cols / relators
    is H_1 and each rewritten v is the image of the original one."""
    import heapq
    rows = {r: v for r, v in enumerate(rels) if v}
    rels.clear()                               # rows now own the dicts
    colrows = {}
    for r, v in rows.items():
        for g in v:
            colrows.setdefault(g, set()).add(r)
    alive = set(range(ngen))
    subs = {}                                  # j -> (order, s, pivot row)
    L = 2
    while True:
        progress = False
        cand = sorted((r for r in rows if len(rows[r]) <= L),
                      key=lambda r: len(rows[r]))
        for r in cand:
            v = rows.get(r)
            if v is None:
                continue
            if not v:
                del rows[r]
                continue
            if len(v) > L:
                continue
            units = [g for g, a in v.items() if a in (1, -1)]
            if not units:
                continue
            j = min(units, key=lambda g: len(colrows.get(g, ())))
            s = v[j]
            piv = dict(v)
            del rows[r]
            for g in piv:
                colrows[g].discard(r)
            for q in list(colrows.get(j, ())):
                row = rows[q]
                f = row[j] * s
                for g, b in piv.items():
                    nv = row.get(g, 0) - f * b
                    if nv:
                        if g not in row:
                            colrows.setdefault(g, set()).add(q)
                        row[g] = nv
                    elif g in row:
                        del row[g]
                        colrows[g].discard(q)
                if not row:
                    del rows[q]
            subs[j] = (len(subs), s, piv)
            alive.discard(j)
            colrows.pop(j, None)
            progress = True
        if progress:
            continue
        lens = [len(v) for v in rows.values()
                if any(a in (1, -1) for a in v.values())]
        if not lens:
            break
        L = max(L + 1, min(lens))
    out = []
    for v0 in vs:
        v = dict(v0)
        heap = [(subs[g][0], g) for g in v if g in subs]
        heapq.heapify(heap)
        while heap:
            _, j = heapq.heappop(heap)
            a = v.get(j)
            if not a:
                continue
            _, s, piv = subs[j]
            f = a * s
            for g, b in piv.items():
                nv = v.get(g, 0) - f * b
                if nv:
                    if g not in v and g in subs:
                        heapq.heappush(heap, (subs[g][0], g))
                    v[g] = nv
                else:
                    v.pop(g, None)
            assert j not in v
        out.append(v)
    cols = sorted(alive)
    return cols, [v for v in rows.values() if v], out


def lattice(cols, Rr, V, mult):
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(Rr, cols)})
    H = incremental_hnf([list(r) for r in Rd], n)
    rank, tors = C.h1_invariants(H, n)
    Vd = C.to_dense(V, cols)
    classes = {}
    for v, m in zip(Vd, mult):
        k = C.reduce_mod_hnf(v, H)
        classes[k] = classes.get(k, 0) + m
    keys = sorted(classes)
    B = C.w_lattice(H, [list(k) for k in keys], n)
    g = 0
    for r in B:
        g = gcd(g, sum(r))
    res = {"h1_rank": rank, "h1_torsion": tors, "classes": len(keys),
           "class_coset_counts": sorted(set(classes.values())),
           "W_rank": len(B), "gcd_aug": g}
    print("  lattice done", res, flush=True)
    # The MILP distance point is only a cross-check (the upper bound
    # d <= d(Gamma(4)) = 1/30 is monotonicity); INDEX2_SKIP_DISTANCE=1 skips it.
    if os.environ.get("INDEX2_SKIP_DISTANCE") != "1":
        t1 = time.time()
        dist = C.distance_milp(B)
        if dist is not None:
            res["d_upper_exact_point"] = str(dist[0])
            res["theta_values"] = sorted(set(dist[1]))
        print(f"  distance MILP {time.time()-t1:.0f}s", flush=True)
    t1 = time.time()
    l1, w = C.best_certificate(B)
    print(f"  certificate MILP {time.time()-t1:.0f}s", flush=True)
    res["cert_l1"], res["cert_aug"] = l1, (sum(w) if w else None)
    res["cert_support"] = sum(1 for a in w if a) if w else None
    return res


def main(out):
    t0 = time.time()
    R = gamma48_basis()
    print("dim Gamma(4)/Gamma(8) seen:", len(R), flush=True)
    assert len(R) == 10
    piv, reps = orbit_reps(R)
    print("orbits of nonzero functionals:", [s for _, s in reps], flush=True)
    results = []
    only = [int(a) for a in sys.argv[2:]] if len(sys.argv) > 2 else None
    for idx, (chi, size) in enumerate(reps):
        if only is not None and idx not in only:
            continue
        objs, act = enumerate_chi(R, piv, chi)
        G.check(act)
        ngen, rels, vs = G.rs(act)
        print(f"[{idx}] chi={chi} orbit {size}: cosets {len(act)}, "
              f"gens {ngen} [{time.time()-t0:.0f}s]", flush=True)
        if os.environ.get("INDEX2_LEAN") == "1":
            cols, Rr, V = lean_eliminate(ngen, rels, vs)
        else:
            cols, Rr, V = C.unit_eliminate(ngen, rels, vs)
        del rels, vs
        print(f"  eliminated: {len(cols)} gens, {len(Rr)} relators "
              f"[{time.time()-t0:.0f}s]", flush=True)
        distinct = {}
        for v in V:
            k = tuple(sorted(v.items()))
            distinct[k] = distinct.get(k, 0) + 1
        keys = list(distinct)
        res = lattice(cols, Rr, [dict(k) for k in keys],
                      [distinct[k] for k in keys])
        res.update({"orbit_index": idx, "chi": list(chi), "orbit_size": size,
                    "cosets": len(act)})
        print(f"[{idx}]", res, f"[{time.time()-t0:.0f}s]", flush=True)
        results.append(res)
        json.dump(results, open(out, "w"), indent=1)
    print("saved", out)


if __name__ == "__main__":
    main(sys.argv[1])
