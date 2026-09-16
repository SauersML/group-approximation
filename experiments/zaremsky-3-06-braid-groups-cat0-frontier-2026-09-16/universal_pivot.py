#!/usr/bin/env python3
"""One-pivot upper bound for the intrinsic distance d_X(P, rho P) in the diagonal link X_n of |NCP_n|.

Usage: python3 universal_pivot.py n [restarts]      (n even; P = {12, 34, ..., (n-1)n}, rho = rotation i -> i+1)

Method.
  * Universal chambers of X_n are chains I_1 < I_2 < ... < I_{m-1} (m = n-1) of one-block partitions whose block
    I_k is a cyclic interval of size k+1. They are indexed by an initial adjacent pair and a left/right extension
    sequence: n * 2^(n-3) chambers.
  * The chamber is the flag W_k = f(I_k) = {y in V : supp y in I_k} of V = {y in R^n : sum y = 0}.
  * For a vertex f(P) of rank r, in any apartment of the building containing f(P) and the chamber W, f(P) is spanned
    by the frame vectors indexed by the jump set S(P, W) = {k : dim f(P) cap W_k > dim f(P) cap W_{k-1}}, and
    dim f(P) cap f(I) = |I| - #(blocks of P, singletons included, meeting I).
    So d_B(P, u) = arccos <p, s> with p = normalize(1_S - (r/m) 1) and s the unit vector of u (non-increasing
    coordinates, sum 0) in R^m.
  * For each universal chamber the script minimises d_B(P, u) + d_B(u, rho P) over u in the closed chamber
    (L-BFGS-B over nonnegative coefficients of the chamber vertices, from every vertex and random starts).
Output: the minimum over universal points u, and the minimising chamber.
If X_n is CAT(1) then d_X(P, rho P) >= pi (the geodesic would be unique, so its midpoint would be fixed by rho, but
no point of X_n is rho-fixed), and by HKS Lemma 4.7 any u with sum < pi gives a path in X_n of that length.
"""
import sys, math, itertools, random
import numpy as np
from scipy.optimize import minimize

n = int(sys.argv[1]); R = int(sys.argv[2]) if len(sys.argv) > 2 else 20
m = n - 1
random.seed(1); np.random.seed(1)

def blocks_with_singletons(nonsing):
    covered = set().union(*nonsing) if nonsing else set()
    return [set(b) for b in nonsing] + [{i} for i in range(n) if i not in covered]

P = [{2 * t, 2 * t + 1} for t in range(n // 2)]          # 0-indexed {12,34,...}
Q = [{(i + 1) % n for i in b} for b in P]                 # rho P = {23,45,...,n1}
BP, BQ = blocks_with_singletons(P), blocks_with_singletons(Q)
rP = n - len(BP); rQ = n - len(BQ)

def universal_chambers():
    out = []
    for a0 in range(n):
        start = [a0, (a0 + 1) % n]
        for ext in itertools.product((0, 1), repeat=n - 3):
            lo, hi = a0, (a0 + 1) % n
            order = list(start)
            for e in ext:
                if e == 0:
                    lo = (lo - 1) % n; order.append(lo)
                else:
                    hi = (hi + 1) % n; order.append(hi)
            rest = [i for i in range(n) if i not in order]
            order += rest
            out.append(order)
    return out

def jump_set(blocks, order):
    S = []
    prev = 0
    for k in range(1, m + 1):
        I = set(order[:k + 1])
        d = len(I) - sum(1 for b in blocks if b & I)
        if d > prev:
            S.append(k)
        prev = d
    return S

def vec(S):
    v = np.zeros(m); v[[k - 1 for k in S]] = 1.0; v -= len(S) / m
    return v / np.linalg.norm(v)

U = np.array([vec(list(range(1, k + 1))) for k in range(1, m)])   # chamber vertices u_1..u_{m-1}

def obj(lam, p, q):
    s = lam @ U
    ns = np.linalg.norm(s)
    if ns < 1e-12:
        return 10.0
    s = s / ns
    return math.acos(max(-1.0, min(1.0, p @ s))) + math.acos(max(-1.0, min(1.0, q @ s)))

best = (1e9, None, None)
vertex_best = 1e9
chambers = universal_chambers()
for order in chambers:
    p, q = vec(jump_set(BP, order)), vec(jump_set(BQ, order))
    starts = [np.eye(m - 1)[k] for k in range(m - 1)] + [np.random.rand(m - 1) for _ in range(R)]
    for k in range(m - 1):
        vertex_best = min(vertex_best, obj(np.eye(m - 1)[k], p, q))
    for x0 in starts:
        res = minimize(obj, x0, args=(p, q), method="L-BFGS-B", bounds=[(0, 1)] * (m - 1))
        if res.fun < best[0]:
            best = (res.fun, order, res.x / max(res.x.max(), 1e-12))

val, order, lam = best
print("n =", n, "| universal chambers:", len(chambers), "| restarts per chamber:", R)
print("min over universal vertices of d_B(P,v)+d_B(v,rho P): %.6f pi" % (vertex_best / math.pi))
print("min over universal points   of d_B(P,u)+d_B(u,rho P): %.6f pi" % (val / math.pi))
print("minimising chamber (order of addition, 1-indexed):", [o + 1 for o in order])
print("coefficients on chamber vertices u_1..u_%d:" % (m - 1), np.round(lam, 4))
p, q = vec(jump_set(BP, order)), vec(jump_set(BQ, order))
print("jump sets S(P,W) =", jump_set(BP, order), " S(rho P, W) =", jump_set(BQ, order),
      " retracted d_A(p,q) = %.6f pi" % (math.acos(max(-1, min(1, p @ q))) / math.pi))
