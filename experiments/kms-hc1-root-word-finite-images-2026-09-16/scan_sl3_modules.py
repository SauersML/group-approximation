#!/usr/bin/env python3
"""Scan 1 (2026-09-16): affine lifts of the SL_3(F_p) image of Gamma_p.

rho(a)=I+E_01, rho(b)=I+E_12, rho(c)=I+E_20 (the k=1 block family of the
2026-09-12 artifact; <a,c> has class 2 here, so this factors through the
A~2 quotient).  For each module M below we compute Z^1(Gamma_p; M) exactly
(Fox calculus, 10 relators) and the rank of delta -> delta(w_p).  A positive
rank certifies a finite image M x| rho(Gamma_p) in which w_p != 1.

Modules: Sym^m(F_p^3) (m=1..p+1) and its dual; permutation modules F_l[Omega]
for Omega = P^2(F_p) points, lines, nonzero vectors, for several primes l.
Usage: scan_sl3_modules.py <p> [l1,l2,...]
"""
import itertools
import sys

import numpy as np

import kmslib as K

p = int(sys.argv[1])
ells = [int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [2, 3, p]


def Eij(n, i, j):
    M = np.eye(n, dtype=np.int64)
    M[i, j] += 1
    return M


base = [Eij(3, 0, 1), Eij(3, 1, 2), Eij(3, 2, 0)]


def monomials(n, m):
    return [e for e in itertools.product(range(m + 1), repeat=n) if sum(e) == m]


def sym_power(g, m, q):
    n = g.shape[0]
    mons = monomials(n, m)
    idx = {e: i for i, e in enumerate(mons)}
    S = np.zeros((len(mons), len(mons)), dtype=np.int64)
    # image of x_j is sum_i g[i,j] x_i
    lin = [{tuple(1 if t == i else 0 for t in range(n)): int(g[i, j]) % q
            for i in range(n) if g[i, j] % q} for j in range(n)]
    for e in mons:
        poly = {tuple([0] * n): 1}
        for j in range(n):
            for _ in range(e[j]):
                new = {}
                for mon, cf in poly.items():
                    for mon2, cf2 in lin[j].items():
                        mm = tuple(x + y for x, y in zip(mon, mon2))
                        new[mm] = (new.get(mm, 0) + cf * cf2) % q
                poly = {k: v for k, v in new.items() if v}
        for mon, cf in poly.items():
            S[idx[mon], idx[e]] = cf
    return S


def perm_module(gens, points, act, q):
    index = {pt: i for i, pt in enumerate(points)}
    mats = []
    for g in gens:
        M = np.zeros((len(points), len(points)), dtype=np.int64)
        for pt in points:
            M[index[act(g, pt)], index[pt]] = 1
        mats.append(M)
    return K.Rep(mats, q)


def normalize(v):
    for x in v:
        if x % p:
            inv = pow(int(x), p - 2, p)
            return tuple(int(y * inv) % p for y in v)
    return None


vecs = [v for v in itertools.product(range(p), repeat=3) if any(v)]
pts = sorted({normalize(v) for v in vecs})


def act_vec(g, v):
    return tuple(int(x) % p for x in g @ np.array(v))


def act_pt(g, v):
    return normalize(act_vec(g, v))


def act_line(g, v):
    # lines as dual vectors: phi -> phi g^{-1}
    gi = K.mat_inv_mod(g, p)
    return normalize(tuple(int(x) % p for x in np.array(v) @ gi))


def report(label, rep):
    rel = rep.check_relators(p)
    ok = all(rel.values())
    P = rep.eval(K.root_word(p))
    wtriv = bool(np.array_equal(P, np.eye(rep.n, dtype=np.int64)))
    if not ok:
        print(label, "RELATOR FAILURE", rel, flush=True)
        return
    dimZ, rk, *_ = K.root_word_translation_rank(rep, p)
    print(f"{label}: dim={rep.n} q={rep.q} relators_ok={ok} rho(w)=I:{wtriv} "
          f"dimZ1={dimZ} rank(delta->delta(w))={rk}", flush=True)


rep3 = K.Rep(base, p)
print("SL3 natural: relators", rep3.check_relators(p), flush=True)
rs = rep3.eval(K.rs_word())
print("rho(rs)-I =\n", (rs - np.eye(3, dtype=np.int64)) % p, flush=True)
for m in range(1, p + 2):
    S = [sym_power(g, m, p) for g in base]
    report(f"Sym^{m}", K.Rep(S, p))
    Sd = [K.mat_inv_mod(M, p).T % p for M in S]
    report(f"Sym^{m} dual", K.Rep(Sd, p))
for ell in ells:
    report(f"F_{ell}[P2 points]", perm_module(base, pts, act_pt, ell))
    report(f"F_{ell}[P2 lines]", perm_module(base, pts, act_line, ell))
    if p <= 7:
        report(f"F_{ell}[nonzero vectors]", perm_module(base, vecs, act_vec, ell))
