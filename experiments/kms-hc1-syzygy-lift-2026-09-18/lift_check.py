#!/usr/bin/env python3
"""Exact check of the right-context lift of u(h)-syzygies (claim
kms-hc1-witt-carry-syzygy-lifts-by-right-freeness).

U = u(h), h = <a,c,e> restricted Heisenberg over F_p, e = ca - ac central,
a^p = c^p = e^p = 0.  PBW basis c^j e^m a^n (0 <= j,m,n < p), multidegree
(deg_a, deg_c) = (m+n, j+m).

B = U (x) U is the free U-bimodule on b (x (x) y <-> x b y).
s1 = 2 a(x)a - 1(x)a^2 - a^2(x)1   (image of the lowest form of [[a,b],a])
s2 = 1(x)c^2 - 2 c(x)c + c^2(x)1   (image of the lowest form of [[b,c],c])
K  = U s1 U + U s2 U,   K+ = U s1 U^+ + U s2 U^+.

Checks, at total (a,c)-multidegree (P,Q):
 FREE : dim (B/K)_(P,Q) = sum_{x+y=(P,Q)} dim V_x dim U_y, V = U/(U a^2 + U c^2)
        (B/K is a free right U-module on a basis of V).
 LIFT : for the syzygies sigma and e_k (k <= p-4) of the syzygy claim,
        R = U1 s1 + U2 s2 lies in K+ (right contexts in U^+), at (P,Q)=(p,p).
 CTRL : a pair (U1,U2) that is NOT a syzygy gives R outside K+.
usage: lift_check.py p [P Q ...]
"""
import sys
import numpy as np
from math import comb, factorial

p = int(sys.argv[1])
extra = [int(x) for x in sys.argv[2:]]
MAXA = MAXC = p


def mdeg(x):
    j, m, n = x
    return (m + n, j + m)


BASIS = [(j, m, n) for j in range(p) for m in range(p) for n in range(p)
         if m + n <= MAXA and j + m <= MAXC]
BYDEG = {}
for x in BASIS:
    BYDEG.setdefault(mdeg(x), []).append(x)
ONE = (0, 0, 0)

_mc = {}


def mul(x, y):
    """PBW product c^j e^m a^n * c^j' e^m' a^n' as dict basis -> coeff mod p."""
    key = (x, y)
    if key in _mc:
        return _mc[key]
    j, m, n = x
    j2, m2, n2 = y
    out = {}
    for r in range(min(n, j2) + 1):
        J, M, N = j + j2 - r, m + m2 + r, n - r + n2
        if J >= p or M >= p or N >= p:
            continue
        co = (-1) ** r * factorial(r) * comb(n, r) * comb(j2, r) % p
        if co:
            out[(J, M, N)] = (out.get((J, M, N), 0) + co) % p
    _mc[key] = out
    return out


def umul(X, Y):  # X, Y dicts in U
    out = {}
    for x, cx in X.items():
        for y, cy in Y.items():
            for z, cz in mul(x, y).items():
                out[z] = (out.get(z, 0) + cx * cy * cz) % p
    return {k: v for k, v in out.items() if v}


def mono(j, m, n, co=1):
    if j >= p or m >= p or n >= p:
        return {}
    return {(j, m, n): co % p}


A1, C1, A2, C2 = mono(0, 0, 1), mono(1, 0, 0), mono(0, 0, 2), mono(2, 0, 0)
S1 = [(2, A1, A1), (-1, {ONE: 1}, A2), (-1, A2, {ONE: 1})]
S2 = [(1, {ONE: 1}, C2), (-2, C1, C1), (1, C2, {ONE: 1})]


def bsand(u, s, v):
    """u * s * v in B for U-dicts u, v and s a list of (coef, left, right)."""
    out = {}
    for co, L, Rt in s:
        for x, cx in umul(u, L).items():
            for y, cy in umul(Rt, v).items():
                out[(x, y)] = (out.get((x, y), 0) + co * cx * cy) % p
    return {k: v for k, v in out.items() if v}


def badd(X, Y, c=1):
    out = dict(X)
    for k, v in Y.items():
        out[k] = (out.get(k, 0) + c * v) % p
    return {k: v for k, v in out.items() if v}


def sub(d, e):
    return (d[0] - e[0], d[1] - e[1])


def gens(P, Q, s, sdeg, plus_only):
    rest = sub((P, Q), sdeg)
    G = []
    for du in BYDEG:
        dv = sub(rest, du)
        if dv not in BYDEG:
            continue
        for u in BYDEG[du]:
            for v in BYDEG[dv]:
                if plus_only and v == ONE:
                    continue
                w = bsand({u: 1}, s, {v: 1})
                if w:
                    G.append(w)
    return G


def echelon(vecs, cols):
    idx = {c: i for i, c in enumerate(cols)}
    M = np.zeros((len(vecs), len(cols)), dtype=np.int64)
    for r, v in enumerate(vecs):
        for k, c in v.items():
            M[r, idx[k]] = c
    piv, rank = [], 0
    for col in range(M.shape[1]):
        if rank == M.shape[0]:
            break
        nz = np.nonzero(M[rank:, col])[0]
        if len(nz) == 0:
            continue
        r = rank + nz[0]
        if r != rank:
            M[[rank, r]] = M[[r, rank]]
        M[rank] = M[rank] * pow(int(M[rank, col]), p - 2, p) % p
        below = M[rank + 1:, col].copy()
        nzb = np.nonzero(below)[0]
        if len(nzb):
            rows = rank + 1 + nzb
            M[rows] = (M[rows] - np.outer(below[nzb], M[rank])) % p
        piv.append(col)
        rank += 1
    return M[:rank], piv, idx


def member(E, piv, idx, v):
    w = np.zeros(E.shape[1] if len(E) else len(idx), dtype=np.int64)
    for k, c in v.items():
        if k not in idx:
            return False
        w[idx[k]] = c
    for i, col in enumerate(piv):
        if w[col]:
            w = (w - w[col] * E[i]) % p
    return not w.any()


def bbasis(P, Q):
    cols = []
    for dx in BYDEG:
        dy = sub((P, Q), dx)
        if dy in BYDEG:
            cols += [(x, y) for x in BYDEG[dx] for y in BYDEG[dy]]
    return cols


def vdim(d):
    """dim of V_d, V = U/(U a^2 + U c^2)."""
    vecs = []
    for s, sd in ((A2, (2, 0)), (C2, (0, 2))):
        du = sub(d, sd)
        for u in BYDEG.get(du, []):
            w = umul({u: 1}, s)
            if w:
                vecs.append(w)
    n = len(BYDEG.get(d, []))
    if not vecs:
        return n
    E, _, _ = echelon(vecs, BYDEG[d])
    return n - len(E)


def free_check(P, Q):
    cols = bbasis(P, Q)
    G = gens(P, Q, S1, (2, 0), False) + gens(P, Q, S2, (0, 2), False)
    E, _, _ = echelon(G, cols)
    lhs = len(cols) - len(E)
    rhs = 0
    for dx in BYDEG:
        dy = sub((P, Q), dx)
        if dy in BYDEG:
            rhs += vdim(dx) * len(BYDEG[dy])
    print(f"FREE p={p} (P,Q)=({P},{Q}) dimB={len(cols)} dim(B/K)={lhs} "
          f"sum dimV*dimU={rhs} {'OK' if lhs == rhs else 'FAIL'}", flush=True)
    return lhs == rhs


def R_of(U1, U2):
    return badd(bsand(U1, S1, {ONE: 1}), bsand(U2, S2, {ONE: 1}))


def lift_check():
    P = Q = p
    cols = bbasis(P, Q)
    G = gens(P, Q, S1, (2, 0), True) + gens(P, Q, S2, (0, 2), True)
    E, piv, idx = echelon(G, cols)
    print(f"LIFT p={p} dimB(p,p)={len(cols)} gens(K+)={len(G)} rank(K+)={len(E)}",
          flush=True)
    ok = True
    # sigma: U2 = 2 c e^(p-3) a^3 + 3 e^(p-2) a^2 ; U1 = 2 c^3 e^(p-3) a - 9 c^2 e^(p-2)
    U2 = badd(mono(1, p - 3, 3, 2), mono(0, p - 2, 2, 3))
    U1 = badd(mono(3, p - 3, 1, 2), mono(2, p - 2, 0, -9))
    syz = badd(umul(U1, A2), umul(U2, C2), -1)
    r = member(E, piv, idx, R_of(U1, U2))
    print(f"  sigma: U1a^2-U2c^2 = {syz or 0}  R in K+ : {r}", flush=True)
    ok &= (not syz) and r
    # e_k, k <= p-4:  U2 = c^(p-2-k) e^k a^(p-k), U1 from U2 c^2 = U1 a^2
    for k in range(1, p - 3):
        U2 = mono(p - 2 - k, k, p - k)
        t = umul(U2, C2)  # = sum_l coef v_l, v_l = c^(p-l) e^l a^(p-l)
        U1 = {}
        for (j, m, n), co in t.items():
            assert n >= 2
            U1 = badd(U1, mono(j, m, n - 2, co))
        syz = badd(umul(U1, A2), t, -1)
        r = member(E, piv, idx, R_of(U1, U2))
        print(f"  e_{k}: syzygy={not syz}  R in K+ : {r}", flush=True)
        ok &= (not syz) and r
    # control: (U1, 0) with U1 a^2 != 0 is not a syzygy; R must lie outside K+
    U1 = mono(2, p - 2, 0)
    r = member(E, piv, idx, R_of(U1, {}))
    print(f"  control (c^2 e^(p-2), 0): U1a^2 != 0 : {bool(umul(U1, A2))}  "
          f"R in K+ : {r}  (expected False)", flush=True)
    ok &= not r
    # control 2: the half-syzygy 3 e_(p-2) alone (no 2 e_(p-3)) is not a syzygy
    U2 = mono(0, p - 2, 2, 3)
    t = umul(U2, C2)
    U1 = {}
    for (j, m, n), co in t.items():
        if n >= 2:
            U1 = badd(U1, mono(j, m, n - 2, co))
    r = member(E, piv, idx, R_of(U1, U2))
    print(f"  control (3 e_(p-2) alone): R in K+ : {r}  (expected False)", flush=True)
    ok &= not r
    return ok


ok = True
pts = [(p, p)] + [(extra[i], extra[i + 1]) for i in range(0, len(extra), 2)]
for P, Q in pts:
    ok &= free_check(P, Q)
ok &= lift_check()
print("ALL OK" if ok else "SOMETHING FAILED")
