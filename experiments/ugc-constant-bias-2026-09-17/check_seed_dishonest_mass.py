#!/usr/bin/env python3
"""Checks for constant-bias-selectors-need-seed-dishonest-witnesses.

Toy doubled LEC: the plain Grassmann 2-to-1 game on F_2^n.
  A-vertices p: l-dim subspaces L; label sigma = a linear functional on L,
     stored as the tuple of its values on the sorted points of L.
  B-vertices q: (l-1)-dim subspaces L'; label tau = functional on L'.
  Constraint e = (L, L') for every hyperplane L' of L, uniform weight.
  pi_e(sigma) = sigma|L'; direction x_e = least point of L minus L';
  ev_e(sigma) = sigma(x_e).  Outer game: one vertex, label alpha in F_2^n,
  <lambda, x_e> = alpha . x_e.

Checks
  (K)  kappa: for each L and each pair sigma != sigma', the fraction of
       hyperplanes L' of L with sigma|L' = sigma'|L' is exactly 1/(2^l - 1).
  (I)  bit-free identity: for every orientation o and every lift labelling
       W = (sigma, tau, b), on every W-satisfied constraint of U_o,
       G_e(tau_q, b_q) = ev_e(sigma_p).
  (F)  Lemma F: D(H, alpha) <= beta(H, alpha) + d + eta + kappa, with the
       honest reference H0 = hon(alpha) (d = eta = 0), where
       D    = mu{ H sat e, ev_e(sigma_p) != alpha . x_e },
       beta = mu{ H sat e, tau_q != alpha|L' }.
       Also the per-vertex form: at each p the mass of H-satisfied,
       seed-honest, ev-dishonest constraints is <= kappa.
  (P)  Prediction step of Theorem C: for every o and W,
       Pr_e[ G_e(tau_q, b_q) = alpha . x_e ] >= val(U_o, W) - D(H, alpha).
Random and structured (honest-then-corrupted) labellings are used.
"""
import itertools, random, sys
from fractions import Fraction

def dot(a, b):
    return bin(a & b).count("1") & 1

def span(vecs):
    s = {0}
    for v in vecs:
        s |= {x ^ v for x in s}
    return frozenset(s)

def subspaces(n, k):
    out = set()
    for vecs in itertools.combinations(range(1, 2 ** n), k):
        S = span(vecs)
        if len(S) == 2 ** k:
            out.add(S)
    return sorted(out, key=lambda S: sorted(S))

def run(n, l, trials, rng):
    A = subspaces(n, l)
    Bs = subspaces(n, l - 1)
    Bidx = {S: i for i, S in enumerate(Bs)}
    # functionals on a subspace S: distinct restrictions of alpha in F_2^n
    def funcs(S):
        pts = sorted(S)
        fs = sorted({tuple(dot(a, x) for x in pts) for a in range(2 ** n)})
        return pts, fs
    Ainfo = [funcs(L) for L in A]
    Binfo = [funcs(Lp) for Lp in Bs]
    edges = []  # (p, q, x_e, restriction map index list)
    for p, L in enumerate(A):
        pts = Ainfo[p][0]
        for Lp in Bs:
            if Lp <= L:
                q = Bidx[Lp]
                x = min(L - Lp)
                qpts = Binfo[q][0]
                pos = [pts.index(y) for y in qpts]
                edges.append((p, q, pts.index(x), pos, x))
    nA, nB, nE = len(A), len(Bs), len(edges)
    kappa = Fraction(1, 2 ** l - 1)
    fails = {"K": 0, "I": 0, "F": 0, "Fp": 0, "P": 0}
    # (K)
    for p, L in enumerate(A):
        fs = Ainfo[p][1]
        hyp = [e for e in edges if e[0] == p]
        for s1, s2 in itertools.combinations(fs, 2):
            c = sum(1 for e in hyp if all(s1[i] == s2[i] for i in e[3]))
            if Fraction(c, len(hyp)) != kappa:
                fails["K"] += 1
    def restrict(sig, e):
        return tuple(sig[i] for i in e[3])
    for t in range(trials):
        alpha = rng.randrange(2 ** n)
        hon_A = [tuple(dot(alpha, x) for x in Ainfo[p][0]) for p in range(nA)]
        hon_B = [tuple(dot(alpha, x) for x in Binfo[q][0]) for q in range(nB)]
        mode = t % 3
        if mode == 0:   # uniformly random labelling
            sig = [rng.choice(Ainfo[p][1]) for p in range(nA)]
            tau = [rng.choice(Binfo[q][1]) for q in range(nB)]
        else:           # honest, then corrupt a random fraction
            r = rng.random()
            sig = [rng.choice(Ainfo[p][1]) if rng.random() < r else hon_A[p]
                   for p in range(nA)]
            tau = [rng.choice(Binfo[q][1]) if (mode == 2 and rng.random() < r)
                   else hon_B[q] for q in range(nB)]
        # random orientation: per edge, per fibre, which element gets bit 0
        o = {}
        for ei, e in enumerate(edges):
            for s in Ainfo[e[0]][1]:
                key = (ei, restrict(s, e))
                if key not in o:
                    o[key] = rng.randrange(2)
        def obit(ei, s):
            e = edges[ei]
            return s[e[2]] ^ o[(ei, restrict(s, e))]
        def G(ei, tq, bq):  # ev of the unique sigma sent to (tq, bq)
            e = edges[ei]
            pre = [s for s in Ainfo[e[0]][1]
                   if restrict(s, e) == tq and obit(ei, s) == bq]
            assert len(pre) == 1
            return pre[0][e[2]]
        b = [rng.randrange(2) for q in range(nB)]
        # optionally align bits to W to raise lift value
        if rng.random() < 0.5:
            for ei, e in enumerate(edges):
                if rng.random() < 0.3:
                    b[e[1]] = obit(ei, sig[e[0]])
        satG = satU = D = beta = agree = 0
        per_p = [0] * nA
        deg_p = [0] * nA
        for ei, e in enumerate(edges):
            p, q = e[0], e[1]
            deg_p[p] += 1
            hs = restrict(sig[p], e) == tau[q]
            us = hs and obit(ei, sig[p]) == b[q]
            evd = sig[p][e[2]] != dot(alpha, e[4])
            seedd = tau[q] != hon_B[q]
            pred = G(ei, tau[q], b[q])
            if us and pred != sig[p][e[2]]:
                fails["I"] += 1
            satG += hs; satU += us
            D += hs and evd
            beta += hs and seedd
            if hs and evd and not seedd:
                per_p[p] += 1
            agree += pred == dot(alpha, e[4])
        if Fraction(D, nE) > Fraction(beta, nE) + kappa:
            fails["F"] += 1
        for p in range(nA):
            if Fraction(per_p[p], deg_p[p]) > kappa:
                fails["Fp"] += 1
        if agree < satU - D:
            fails["P"] += 1
    return nA, nB, nE, fails

def main():
    rng = random.Random(20260917)
    total = 0
    for (n, l, trials) in [(3, 2, 300), (4, 2, 300), (4, 3, 150), (5, 3, 20)]:
        nA, nB, nE, fails = run(n, l, trials, rng)
        print(f"n={n} l={l}: |A|={nA} |B|={nB} |E|={nE} trials={trials} fails={fails}")
        total += sum(fails.values())
    print("TOTAL FAILURES", total)
    sys.exit(1 if total else 0)

if __name__ == "__main__":
    main()
