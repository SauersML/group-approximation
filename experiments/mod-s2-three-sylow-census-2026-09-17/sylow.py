#!/usr/bin/env python3
"""Torelli census along the 3-Sylow chain from Gamma(2) toward Gamma(6).

For a subgroup V of the upper unipotent 3-Sylow U of Sp_4(F_3) put
    Gamma_V = { A in Sp_4(Z) : A = I mod 2, A mod 3 in V }.
[Gamma(2) : Gamma_U] = 640 is prime to 3, and Gamma_U > Gamma_V > Gamma(6) with
3-power indices, so the chain V = U > ... > 1 is the part of the passage
Gamma(2) -> Gamma(6) where transfer certificates die (3 | index).

Reduction as in ../mod-s2-gamma4-torsion-census-2026-09-17/gamma4.py:
-I is not in Gamma_V, so M_V = pi^-1(Gamma_V) embeds in Mod(S_{0,6}); its
image is the stabilizer in H = B_5/<<Delta^2>> of the coset L X, where
L = {I} x (+-V) inside Sp_4(Z/2) x Sp_4(F_3) and X is the image of an element.
The coset L X is keyed by (X mod 2, min over u in +-V of u X mod 3).

Usage: python3 sylow.py <name> [out.json]
  name: U        (V = U, 38400 cosets)
        max<k>   (V = k-th maximal subgroup of U, 115200 cosets)
Requires python-flint, numpy, scipy, sympy.
"""
import itertools
import json
import os
import sys
import time
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-gamma4-torsion-census-2026-09-17"))
import census as C  # noqa: E402
import gamma4 as G  # noqa: E402
from gamma4_lattice import incremental_hnf  # noqa: E402

J3 = C.J % 3
POW3 = 3 ** np.arange(16, dtype=np.int64)


def key3(A):
    if A.ndim == 2:
        return int((A.reshape(16) % 3) @ POW3)
    return (A.reshape(-1, 16) % 3) @ POW3


def unkey3(k):
    d = [(k // int(p)) % 3 for p in POW3]
    return np.array(d, dtype=np.int64).reshape(4, 4)


def sp4_f3():
    """All of Sp_4(F_3), by closure under the chain transvections."""
    gens = [A % 3 for A in C.GENMATS]
    start = np.eye(4, dtype=np.int64)
    seen = {key3(start)}
    queue = [start]
    for X in queue:
        for B in gens:
            Y = (X @ B) % 3
            k = key3(Y)
            if k not in seen:
                seen.add(k)
                queue.append(Y)
    assert len(queue) == 51840, len(queue)
    return queue


def sylow_U(allg):
    """Row-action flag a1 < <a1,a2>: e0 A = e0 and e2 A = e2 mod <e0>."""
    e0 = np.array([1, 0, 0, 0])
    U = []
    for A in allg:
        r0 = (e0 @ A) % 3
        r2 = A[2] % 3
        if (r0 == e0).all() and r2[1] == 0 and r2[2] == 1 and r2[3] == 0:
            U.append(A)
    assert len(U) == 81, len(U)
    return U


def subgroup_closure(gens):
    I = np.eye(4, dtype=np.int64)
    seen = {key3(I)}
    queue = [I]
    for X in queue:
        for B in gens:
            Y = (X @ B) % 3
            k = key3(Y)
            if k not in seen:
                seen.add(k)
                queue.append(Y)
    return queue


def frattini_maximals(U):
    """Maximal subgroups of the 3-group U (index 3, containing Phi(U))."""
    keys = {key3(A) for A in U}
    inv = {}
    for A in U:
        for B in U:
            if key3((A @ B) % 3) == key3(np.eye(4, dtype=np.int64)):
                inv[key3(A)] = B
    comms = [(A @ B @ inv[key3(A)] @ inv[key3(B)]) % 3 for A in U for B in U]
    cubes = [np.linalg.matrix_power(A, 3) % 3 for A in U]
    Phi = subgroup_closure(comms + cubes)
    phik = {key3(A) for A in Phi}
    assert phik <= keys
    q = len(U) // len(Phi)
    r = round(np.log(q) / np.log(3))
    # maximal subgroups: closures of Phi with all but one direction
    assert r == 2, r          # then Phi<A> is maximal for every A outside Phi
    maxes, found = [], set()
    for A in U:
        if key3(A) in phik:
            continue
        M = subgroup_closure(list(Phi) + [A])
        assert len(M) == len(U) // 3
        fk = frozenset(key3(X) for X in M)
        if fk not in found:
            found.add(fk)
            maxes.append(M)
    maxes.sort(key=lambda M: sorted(key3(X) for X in M))
    return Phi, r, maxes


def coset_action(V):
    """Right action of s1..s4 on cosets L X of H."""
    pmV = np.array([u % 3 for u in V] + [(-u) % 3 for u in V],
                   dtype=np.int64)
    mats = [C.GENMATS[i] for i in range(G.NG)]

    def canon(X):
        X2 = tuple(int(t) % 2 for t in X.flatten())
        prods = np.einsum("uij,jk->uik", pmV, X % 3) % 3
        return (X2, int(key3(prods).min()))

    start = np.eye(4, dtype=np.int64)
    k0 = canon(start)
    index, reps, act = {k0: 0}, [start], []
    q = 0
    while q < len(reps):
        X = reps[q]
        row = []
        for B in mats:
            Y = (X @ B) % 6
            k = canon(Y)
            if k not in index:
                index[k] = len(reps)
                reps.append(Y)
            row.append(index[k])
        act.append(row)
        q += 1
    return act


def positive_certificate(B):
    """A_+ : least aug(w) over w in W, w >= 0, aug(w) prime to 3."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(B, dtype=float)
    r, m = Bf.shape
    best = (None, None)
    aug = Bf.sum(axis=1)
    for res3 in (1, 2):
        # variables y (r), q (1); w = B^T y >= 0; aug = 3q + res3
        c = np.concatenate([aug, [0.0]])
        cons = [LinearConstraint(np.hstack([Bf.T, np.zeros((m, 1))]),
                                 0, np.inf),
                LinearConstraint(np.concatenate([aug, [-3.0]])[None, :],
                                 res3, res3)]
        res = milp(c, constraints=cons, integrality=np.ones(r + 1),
                   bounds=Bounds(np.full(r + 1, -1e6), np.full(r + 1, 1e6)),
                   options={"time_limit": 900})
        if res.x is None:
            continue
        y = [int(round(v)) for v in res.x[:r]]
        w = [sum(B[i][j] * y[i] for i in range(r)) for j in range(m)]
        assert min(w) >= 0 and sum(w) % 3 == res3
        if best[0] is None or sum(w) < best[0]:
            best = (sum(w), w)
    return best


def lattice_stage(act, label):
    t0 = time.time()
    G.check(act)
    ngen, rels, vs = G.rs(act)
    print(f"[{label}] cosets {len(act)}, Schreier gens {ngen}, relators "
          f"{len(rels)} [{time.time()-t0:.0f}s]", flush=True)
    return lattice_from_rs(ngen, rels, vs, label, len(act))


def lattice_from_rs(ngen, rels, vs, label, ncosets, elim=None):
    t0 = time.time()
    if elim is None:
        elim = C.unit_eliminate
    cols, R, V = elim(ngen, rels, vs)
    n = len(cols)
    print(f"[{label}] after unit elimination {n} gens, {len(R)} relators "
          f"[{time.time()-t0:.0f}s]", flush=True)
    # dedupe sparsely, then HNF in dense chunks (never the full dense matrix)
    Rs = sorted({tuple(sorted(v.items())) for v in R})
    H = []
    chunk = 3000
    for k in range(0, len(Rs), chunk):
        block = C.to_dense([dict(t) for t in Rs[k:k + chunk]], cols)
        H = C.hnf_rows(H + block, n)
    rank, tors = C.h1_invariants(H, n)
    print(f"[{label}] H_1 = Z^{rank} + {tors} [{time.time()-t0:.0f}s]",
          flush=True)
    Vd = C.to_dense(V, cols)
    classes, cls_of = {}, []
    for v in Vd:
        key = C.reduce_mod_hnf(v, H)
        if key not in classes:
            classes[key] = len(classes)
        cls_of.append(classes[key])
    keys = sorted(classes, key=lambda k: classes[k])
    counts = [0] * len(keys)
    for c in cls_of:
        counts[c] += 1
    B = C.w_lattice(H, [list(k) for k in keys], n)
    m = len(keys)
    g = 0
    for a in (sum(r) for r in B):
        g = gcd(g, a)
    out = {"label": label, "cosets": ncosets, "schreier_gens": ngen,
           "gens_after_unit_elim": n, "h1_rank": rank, "h1_torsion": tors,
           "classes": m, "class_coset_counts": sorted(set(counts)),
           "W_rank": len(B), "gcd_aug_W": g}
    print(f"[{label}] classes {m}, W rank {len(B)}, gcd aug {g} "
          f"[{time.time()-t0:.0f}s]", flush=True)
    if B:
        dist = C.distance_milp(B)
        if dist is not None:
            out["d"] = str(dist[0])
            out["theta_values"] = sorted(set(dist[1]))
        l1, w = C.best_certificate(B)
        out["cert_l1"] = l1
        out["cert_aug"] = sum(w) if w else None
        ap, wp = positive_certificate(B)
        out["A_plus"] = ap
        out["A_plus_support"] = sum(1 for a in wp if a) if wp else None
        out["A_plus_multiplicities"] = (sorted(a for a in wp if a)
                                        if wp else None)
    out["seconds"] = round(time.time() - t0)
    print(f"[{label}] {json.dumps(out)}", flush=True)
    return out, (cols, H, keys, cls_of, B)


def subgroup(name):
    allg = sp4_f3()
    U = sylow_U(allg)
    if name == "U":
        return U
    Phi, r, maxes = frattini_maximals(U)
    print(f"Frattini quotient of U: F_3^{r}; {len(maxes)} maximal subgroups",
          flush=True)
    if name.startswith("max"):
        return maxes[int(name[3:])]
    if name == "phi":
        return Phi
    if name == "z":
        # centre of U (order 3 for the 3-Sylow of Sp_4(F_3))
        Z = [A for A in U
             if all(key3((A @ B) % 3) == key3((B @ A) % 3) for B in U)]
        print(f"|Z(U)| = {len(Z)}", flush=True)
        return Z
    if name.startswith("phisub"):
        # order-3 subgroups of Phi(U), sorted by key
        subs, found = [], set()
        for A in Phi:
            if key3(A) == key3(np.eye(4, dtype=np.int64)):
                continue
            Sg = subgroup_closure([A])
            fk = frozenset(key3(X) for X in Sg)
            if len(Sg) == 3 and fk not in found:
                found.add(fk)
                subs.append(Sg)
        subs.sort(key=lambda M: sorted(key3(X) for X in M))
        print(f"order-3 subgroups of Phi(U): {len(subs)}", flush=True)
        return subs[int(name[6:])]
    if name == "one":
        return [np.eye(4, dtype=np.int64)]
    raise ValueError(name)


if __name__ == "__main__":
    name = sys.argv[1]
    outp = sys.argv[2] if len(sys.argv) > 2 else \
        os.path.join(HERE, f"sylow-{name}.json")
    V = subgroup(name)
    t0 = time.time()
    act = coset_action(V)
    print(f"[{name}] |V| = {len(V)}, cosets {len(act)} "
          f"[{time.time()-t0:.0f}s]", flush=True)
    out, _ = lattice_stage(act, name)
    out["V_order"] = len(V)
    json.dump(out, open(outp, "w"), indent=1)
    print("saved", outp)
