#!/usr/bin/env python3
"""Separating-twist relation lattices strictly between level 4 and level 8.

Every subgroup G with K8 <= G <= K4 of Pbar = PMod(S_{0,6}) (equivalently,
every Gamma' with Gamma(8) <= Gamma' <= Gamma(4), as the preimage contains
Torelli) is normal in Pbar, because Gamma(2) acts trivially by conjugation
on Gamma(4)/Gamma(8) = sp_4(F_2):
    (I + 2Y)(I + 4X)(I + 2Y)^-1 = I + 4X  (mod 8).
So G is determined by a subspace S of sp_4(F_2) = {X : JX symmetric mod 2},
G/K8 = {I + 4X : X in S}, and the cosets Pbar/G are matrices M mod 8 in
Gamma(2) up to sign and M -> M + 4X (X in S).  [K4 : G] = 2^codim S.

S = Alt = {X : JX alternating} is Sp_4(F_2)-invariant, of codimension 4,
and is Igusa's Gamma(4,8) (diag(A B^T), diag(C D^T) = 0 mod 8).

For each S we compute H_1(G), the separating classes, W, gcd aug,
d = dist_inf((1/3)1, W^perp), the signed l1 certificate, and the minimal
POSITIVE relation (all exponents >= 0) with exponent sum prime to 3.
"""
import itertools
import json
import os
import random
import sys
import time
from math import gcd

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..",
                                "mod-s2-torelli-scalar-census-2026-09-17"))
import census as C  # noqa: E402
import pure as P  # noqa: E402

NP = len(P.PAIRS)
J = C.J


def sigma_mat(a):
    x = C.CHAIN[abs(a) - 1]
    return np.eye(4, dtype=np.int64) + (1 if a > 0 else -1) * np.outer(x, x @ J)


def pure_mats():
    out = []
    for p in range(NP):
        A = np.eye(4, dtype=np.int64)
        for a in P.pure_to_sigma((p + 1,)):
            A = A @ sigma_mat(a)
        assert ((A - np.eye(4, dtype=np.int64)) % 2 == 0).all()
        out.append(A)
    return out


def rref2(rows):
    A = [[int(t) % 2 for t in r] for r in rows]
    m = len(A)
    ncol = len(A[0]) if A else 0
    pr = 0
    for col in range(ncol):
        sel = next((r for r in range(pr, m) if A[r][col]), None)
        if sel is None:
            continue
        A[pr], A[sel] = A[sel], A[pr]
        for r in range(m):
            if r != pr and A[r][col]:
                A[r] = [(a + b) % 2 for a, b in zip(A[r], A[pr])]
        pr += 1
    return tuple(tuple(r) for r in A[:pr])


def sp4_f2_basis():
    J2 = J % 2
    sols = []
    for bits in itertools.product((0, 1), repeat=16):
        X = np.array(bits).reshape(4, 4)
        Y = (J2 @ X) % 2
        if (Y == Y.T).all():
            sols.append(X.flatten())
    basis = rref2(sols)
    assert len(basis) == 10
    return [np.array(b) for b in basis]


def alt_subspace():
    J2 = J % 2
    out = []
    for bits in itertools.product((0, 1), repeat=16):
        X = np.array(bits).reshape(4, 4)
        Y = (J2 @ X) % 2
        if (Y == Y.T).all() and not Y.diagonal().any():
            out.append(X.flatten())
    return rref2(out)


def make_canon(S):
    S = [np.array(b) % 2 for b in S]
    piv = [int(np.nonzero(b)[0][0]) for b in S]

    def red(v):
        v = v % 2
        for b, p in zip(S, piv):
            if v[p]:
                v = (v + b) % 2
        return v

    def one(M):
        M = M % 8
        M0 = M % 4
        M1 = ((M - M0) // 4).flatten()
        return tuple(M0.flatten()) + tuple(red(M1))

    def canon(M):
        return min(one(M), one(-M))
    return canon


def enumerate_cosets(S, limit=300000):
    mats = pure_mats()
    canon = make_canon(S)
    start = canon(np.eye(4, dtype=np.int64))
    index, reps, act = {start: 0}, [np.eye(4, dtype=np.int64)], []
    q = 0
    while q < len(reps):
        A = reps[q]
        row = []
        for B in mats:
            nb = (A @ B) % 8
            key = canon(nb)
            if key not in index:
                index[key] = len(reps)
                reps.append(nb)
                if len(reps) > limit:
                    raise RuntimeError("too many cosets")
            row.append(index[key])
        act.append(row)
        q += 1
    return act


def schreier(act):
    k = len(act)
    seen = [False] * k
    seen[0] = True
    tree = set()
    queue = [0]
    for c in queue:
        for p in range(NP):
            d = act[c][p]
            if not seen[d]:
                seen[d] = True
                tree.add((c, p))
                queue.append(d)
    assert all(seen)
    gen = {}
    for c in range(k):
        for p in range(NP):
            if (c, p) not in tree:
                gen[(c, p)] = len(gen)
    return gen


_INV = {}


def inverse_action(act):
    key = id(act)
    if key not in _INV:
        inv = [[None] * NP for _ in act]
        for c, row in enumerate(act):
            for p, d in enumerate(row):
                inv[d][p] = c
        _INV[key] = (act, inv)
    return _INV[key][1]


def trace(act, gen, word, c, vec):
    """Abelianised Schreier rewriting.  An inverse letter A_p^-1 at coset c
    moves to the coset d with act[d][p] = c (NOT act[c][p]: the pure
    generators act as involutions only on the level-4 cosets)."""
    inv = inverse_action(act)
    for a in word:
        p = abs(a) - 1
        if a > 0:
            d = act[c][p]
            g = gen.get((c, p))
            if g is not None:
                vec[g] = vec.get(g, 0) + 1
        else:
            d = inv[c][p]
            g = gen.get((d, p))
            if g is not None:
                vec[g] = vec.get(g, 0) - 1
        c = d
    return c


def positive_min(B, r_mod3, time_limit=900):
    """min sum w over w = B^T y >= 0 integral with sum w = 3q + r_mod3."""
    from scipy.optimize import Bounds, LinearConstraint, milp
    Bf = np.array(B, dtype=float)
    r, m = Bf.shape
    # variables y (r ints), q (int)
    aug = Bf.sum(axis=1)
    c = np.concatenate([aug, [0.0]])
    cons = [LinearConstraint(np.concatenate([aug, [-3.0]])[None, :],
                             r_mod3, r_mod3),
            LinearConstraint(np.hstack([Bf.T, np.zeros((m, 1))]), 0, np.inf)]
    res = milp(c, constraints=cons, integrality=np.ones(r + 1),
               bounds=Bounds(np.full(r + 1, -1e6), np.full(r + 1, 1e6)),
               options={"time_limit": time_limit})
    if res.x is None:
        return None, None
    y = [int(round(v)) for v in res.x[:r]]
    w = [sum(B[i][j] * y[i] for i in range(r)) for j in range(m)]
    assert min(w) >= 0 and sum(w) % 3 == r_mod3
    return sum(w), w


def run(S, label, milp=True):
    t0 = time.time()
    act = enumerate_cosets(S)
    k = len(act)
    gen = schreier(act)
    rels = [(u, v) for u, v in P.check_presentation()]
    rels.append((P.delta2_pure(), ()))
    rows = []
    for u, v in rels:
        w = tuple(u) + P.finv(v)
        for c in range(k):
            vec = {}
            assert trace(act, gen, w, c, vec) == c
            vec = {g: a for g, a in vec.items() if a}
            if vec:
                rows.append(vec)
    tab = P.conj_table()
    TW = P.standard_twists(tab)
    vs, owner = [], []
    for ti, t in enumerate(P.TRIPLES):
        sq = TW[t] * 2
        for c in range(k):
            vec = {}
            assert trace(act, gen, sq, c, vec) == c
            vs.append({g: a for g, a in vec.items() if a})
            owner.append(ti)
    print(f"[{label}] cosets {k}, gens {len(gen)}, relators {len(rows)} "
          f"[{time.time()-t0:.1f}s]", flush=True)
    cols, R, V = C.unit_eliminate(len(gen), rows, vs)
    del rows
    n = len(cols)
    Rd = sorted({tuple(r) for r in C.to_dense(R, cols)})
    H = C.hnf_rows([list(r) for r in Rd], n)
    rank, tors = C.h1_invariants(H, n)
    print(f"[{label}] H_1 = Z^{rank} + {tors}  ({n} gens) "
          f"[{time.time()-t0:.1f}s]", flush=True)
    Vd = C.to_dense(V, cols)
    classes = {}
    for v, o in zip(Vd, owner):
        key = C.reduce_mod_hnf(v, H)
        classes.setdefault(key, o)
    keys = sorted(classes)
    per = {}
    for kk in keys:
        per[classes[kk]] = per.get(classes[kk], 0) + 1
    B = C.w_lattice(H, [list(x) for x in keys], n)
    g = 0
    for r in B:
        g = gcd(g, sum(r))
    res = {"label": label, "codim_S_in_sp4F2": 10 - len(S),
           "cosets_in_Pbar": k, "h1_rank": rank, "h1_torsion": tors,
           "classes": len(keys),
           "classes_per_splitting": sorted(set(per.values())),
           "W_rank": len(B), "gcd_aug": g}
    print(res, f"[{time.time()-t0:.1f}s]", flush=True)
    if milp and B:
        dist = C.distance_milp(B)
        if dist is not None:
            res["d"] = str(dist[0])
        l1, w = C.best_certificate(B)
        res["signed_cert_l1"] = l1
        pos = {}
        for rm in (1, 2):
            s, w = positive_min(B, rm)
            pos[rm] = s
            if s is not None:
                res[f"positive_min_aug_{rm}mod3"] = s
                res[f"positive_min_aug_{rm}mod3_support"] = sum(
                    1 for a in w if a)
                res[f"positive_min_aug_{rm}mod3_splittings"] = sorted(
                    {classes[keys[j]] for j, a in enumerate(w) if a})
        print(res, f"[{time.time()-t0:.1f}s]", flush=True)
    return res


def random_S(codim, rng):
    basis = sp4_f2_basis()
    while True:
        fs = [np.array([rng.randint(0, 1) for _ in range(10)])
              for _ in range(codim)]
        F = np.array(fs) % 2
        if len(rref2(F)) == codim:
            break
    # S = {sum c_i b_i : F c = 0}
    ker = []
    for c in itertools.product((0, 1), repeat=10):
        if not ((F @ np.array(c)) % 2).any():
            ker.append(sum(ci * b for ci, b in zip(c, basis)) % 2)
    return [np.array(v) for v in rref2(ker)]


if __name__ == "__main__":
    which = sys.argv[1]
    out = sys.argv[2]
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    if which == "gamma4":
        S = [np.array(b) for b in sp4_f2_basis()]
    elif which == "igusa48":
        S = [np.array(b) for b in alt_subspace()]
    elif which.startswith("random"):
        S = random_S(int(which[6:]), rng)
    res = run(S, which)
    json.dump(res, open(out, "w"), indent=1)
    print("saved", out)
