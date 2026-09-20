#!/usr/bin/env python3
"""Exact-enumeration check of the pi-weighted coset Gram identity for the
fibre-summed connectivity kernel sigma^N_p on Q = Gamma/N.

Node: research/fpbs-fibre-mass-positive-definite-in-gap-window.md

For Bernoulli(p) bond percolation on a finite Cayley graph Cay(Gamma,{r,s}) of
a dihedral group and a normal subgroup N, put

    A_C(v) = |C ∩ vN|                      (v a coset),
    sigma(q) = E A_{K_e}(q),
    W_pi(C) = sum_r pi_r A_C(r)            (pi a full-support probability on Q),

and, for an N-invariant cluster functional psi,

    sigma_psi(q) = E[ A_{K_e}(q) psi(K_e) ].

Checked, for every pair of cosets u, w:

 (T)  translation:   E A_{K_{y_u}}(w) = sigma(u^{-1} w)
 (G)  Gram identity: sigma_psi(u^{-1} w)
                      = sum_v pi_v E[ A_{K_{y_v}}(u) A_{K_{y_v}}(w) psi / W_pi(K_{y_v}) ]
      for psi = 1 and psi = 1{|C| >= m}, for several random pi;
 (P)  the matrix [sigma_psi(u^{-1} w)]_{u,w} is positive semidefinite;
 (M)  maximality: E[A_{K_e}(q)^2 / A_{K_e}(e)] = E[A_{K_{y_q}}(q); K_{y_q} meets N]
      <= sigma(e), and sigma(q) <= sigma(e);
 (X)  the naive root normalised by A(e) alone,
      E[A_{K_e}(u) A_{K_e}(w) / A_{K_e}(e)], is NOT sigma(u^{-1} w).

D_4 is done in exact rational arithmetic; D_6 in floating point.
On a finite group (P) is automatic; the content being tested is the exact
identity (G), whose proof is the same coset mass-transport step used on
infinite groups.
"""
from fractions import Fraction
import itertools
import random
import sys

import numpy as np


def dihedral(n):
    els = [(k, e) for e in range(2) for k in range(n)]
    idx = {g: i for i, g in enumerate(els)}

    def mul(a, b):
        k1, e1 = a
        k2, e2 = b
        return ((k1 + (-1) ** e1 * k2) % n, (e1 + e2) % 2)

    def inv(a):
        k, e = a
        return ((-k) % n, 0) if e == 0 else a

    return els, idx, mul, inv


def cayley_edges(els, idx, mul, gens):
    edges = set()
    for x in els:
        for g in gens:
            y = mul(x, g)
            edges.add(tuple(sorted((idx[x], idx[y]))))
    return sorted(edges)


def clusters(nv, edges, mask):
    parent = list(range(nv))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for j, (a, b) in enumerate(edges):
        if mask >> j & 1:
            ra, rb = find(a), find(b)
            if ra != rb:
                parent[ra] = rb
    lab = [find(a) for a in range(nv)]
    return lab


def run(n, N_gens_desc, N_set, p, exact, pis, psi_m, out):
    els, idx, mul, inv = dihedral(n)
    nv = len(els)
    r, s = (1, 0), (0, 1)
    edges = cayley_edges(els, idx, mul, [r, s])
    ne = len(edges)
    Nset = set(N_set)
    # check normality
    for g in els:
        for h in Nset:
            assert mul(mul(g, h), inv(g)) in Nset, "N not normal"
    # cosets
    coset_of = {}
    reps = []
    for g in els:
        key = frozenset(mul(g, h) for h in Nset)
        if key not in coset_of:
            coset_of[key] = len(reps)
            reps.append(g)
    cos = [coset_of[frozenset(mul(g, h) for h in Nset)] for g in els]
    nq = len(reps)
    # quotient multiplication via representatives
    def qmul_inv(u, w):  # coset of y_u^{-1} y_w
        return cos[idx[mul(inv(reps[u]), reps[w])]]

    e_idx = idx[(0, 0)]
    yrep = [idx[g] for g in reps]
    num = Fraction if exact else float
    P = num(p) if exact else float(p)
    one = num(1)

    zero = num(0)
    sigma = {m: [zero] * nq for m in [None] + psi_m}
    trans = [[zero] * nq for _ in range(nq)]
    gram = {(m, k): [[zero] * nq for _ in range(nq)]
            for m in [None] + psi_m for k in range(len(pis))}
    wrong = [[zero] * nq for _ in range(nq)]
    maxlhs = [zero] * nq
    maxrhs = [zero] * nq

    powP = [P ** j for j in range(ne + 1)]
    powQ = [(one - P) ** j for j in range(ne + 1)]
    for mask in range(1 << ne):
        k = bin(mask).count("1")
        wt = powP[k] * powQ[ne - k]
        lab = clusters(nv, edges, mask)
        # A[root][v]
        A = {}
        size = {}
        for x in range(nv):
            A.setdefault(lab[x], [0] * nq)[cos[x]] += 1
            size[lab[x]] = size.get(lab[x], 0) + 1
        Ke = lab[e_idx]
        for m in [None] + psi_m:
            ps = 1 if m is None else (1 if size[Ke] >= m else 0)
            if ps:
                for q in range(nq):
                    sigma[m][q] += wt * A[Ke][q]
        for u in range(nq):
            Ku = lab[yrep[u]]
            for w in range(nq):
                trans[u][w] += wt * A[Ku][w]
        # Gram right-hand sides
        for kk, pi in enumerate(pis):
            for v in range(nq):
                Kv = lab[yrep[v]]
                Av = A[Kv]
                W = sum(pi[t] * Av[t] for t in range(nq))
                for m in [None] + psi_m:
                    ps = 1 if m is None else (1 if size[Kv] >= m else 0)
                    if not ps:
                        continue
                    fac = wt * pi[v] / W
                    G = gram[(m, kk)]
                    for u in range(nq):
                        if Av[u]:
                            for w in range(nq):
                                G[u][w] += fac * Av[u] * Av[w]
        Ae = A[Ke]
        for u in range(nq):
            for w in range(nq):
                wrong[u][w] += wt * Ae[u] * Ae[w] / num(Ae[cos[e_idx]])
        for q in range(nq):
            maxlhs[q] += wt * num(Ae[q]) ** 2 / num(Ae[cos[e_idx]])
            Kq = lab[yrep[q]]
            if A[Kq][cos[e_idx]] > 0:
                maxrhs[q] += wt * A[Kq][q]

    def eq(a, b):
        return a == b if exact else abs(float(a) - float(b)) < 1e-10

    ok = True
    out.append(f"--- D_{n}, N = {N_gens_desc} (|N| = {len(Nset)}, |Q| = {nq}), "
               f"p = {p}, edges = {ne}, configs = {1 << ne}, "
               f"{'exact' if exact else 'float'}")
    s0 = sigma[None]
    out.append("sigma(q) over cosets q: " + ", ".join(
        f"{float(x):.6f}" for x in s0))
    # (T)
    tr_ok = all(eq(trans[u][w], s0[qmul_inv(u, w)])
                for u in range(nq) for w in range(nq))
    out.append(f"(T) translation E A_(K_(y_u))(w) = sigma(u^-1 w): {tr_ok}")
    ok &= tr_ok
    # (G)
    for m in [None] + psi_m:
        lab_m = "psi = 1" if m is None else f"psi = 1{{|C| >= {m}}}"
        sm = sigma[m]
        for kk in range(len(pis)):
            G = gram[(m, kk)]
            g_ok = all(eq(G[u][w], sm[qmul_inv(u, w)])
                       for u in range(nq) for w in range(nq))
            out.append(f"(G) Gram identity, {lab_m}, pi #{kk}: {g_ok}")
            ok &= g_ok
        M = np.array([[float(sm[qmul_inv(u, w)]) for w in range(nq)]
                      for u in range(nq)])
        ev = np.linalg.eigvalsh((M + M.T) / 2)
        out.append(f"(P) min eigenvalue of [sigma_psi(u^-1 w)], {lab_m}: "
                   f"{ev.min():.3e} (symmetric: {np.allclose(M, M.T)})")
        ok &= ev.min() > -1e-12
    # (M)
    m_ok = all(eq(maxlhs[q], maxrhs[q]) for q in range(nq))
    b_ok = all(float(maxrhs[q]) <= float(s0[cos[e_idx]]) + 1e-15
               and float(s0[q]) <= float(s0[cos[e_idx]]) + 1e-15
               for q in range(nq))
    out.append(f"(M) transport E[A(q)^2/A(e)] = E[A_(K_(y_q))(q); meets N]: {m_ok};"
               f" bounds <= sigma(e): {b_ok}")
    ok &= m_ok and b_ok
    # (X)
    diffs = [abs(float(wrong[u][w]) - float(s0[qmul_inv(u, w)]))
             for u in range(nq) for w in range(nq)]
    out.append(f"(X) naive A(e)-normalised root: max |error| = {max(diffs):.6f} "
               f"(nonzero means the naive formula is false)")
    ok &= (max(diffs) > 1e-6) or nq == 1
    out.append(f"ALL CHECKS PASS: {ok}")
    return ok


def main():
    random.seed(20260917)
    out = []
    allok = True

    def rand_pi(nq, exact):
        ws = [random.randint(1, 9) for _ in range(nq)]
        tot = sum(ws)
        return [Fraction(w, tot) if exact else w / tot for w in ws]

    # D_4 exact
    n = 4
    cases4 = [
        ("<r^2>", [(0, 0), (2, 0)]),
        ("<r>", [(k, 0) for k in range(4)]),
        ("<r^2, s>", [(0, 0), (2, 0), (0, 1), (2, 1)]),
    ]
    for desc, Nset in cases4:
        els_count = 8
        nq = els_count // len(Nset)
        for p in [Fraction(1, 3), Fraction(3, 5)]:
            pis = [rand_pi(nq, True) for _ in range(2)]
            allok &= run(n, desc, Nset, p, True, pis, [3, 5], out)
    # D_6 float
    n = 6
    cases6 = [
        ("<r^3>", [(0, 0), (3, 0)]),
        ("<r^2>", [(0, 0), (2, 0), (4, 0)]),
    ]
    for desc, Nset in cases6:
        nq = 12 // len(Nset)
        pis = [rand_pi(nq, False) for _ in range(2)]
        allok &= run(n, desc, Nset, 0.45, False, pis, [4], out)
    out.append(f"\nOVERALL: {'PASS' if allok else 'FAIL'}")
    print("\n".join(out))
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
