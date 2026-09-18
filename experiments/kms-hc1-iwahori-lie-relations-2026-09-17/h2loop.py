#!/usr/bin/env python3
"""Graded Lie algebra homology H_1, H_2 of L = n^+(sl3) + t sl3[t] over F_p (principal grading:
deg E_ij t^n = 3n + j - i, deg t^n h = 3n).  dim H_2(L)_k = number of minimal Lie relations of L in degree k
(L is generated in degree 1 by e1=E12, e2=E23, e0=E31 t).
Usage: h2loop.py p maxdeg"""
import sys, itertools
import numpy as np
p = int(sys.argv[1]); K = int(sys.argv[2])

def basis(k):
    B = []
    n, r = divmod(k, 3)
    for i in range(3):
        for j in range(3):
            if i != j and (k - (j - i)) % 3 == 0:
                m = (k - (j - i)) // 3
                if m >= 0: B.append(('e', m, i, j))
    if r == 0 and n >= 1:
        B += [('h', n, 0), ('h', n, 1)]
    return B

Bs = {k: basis(k) for k in range(1, K + 1)}
idx = {k: {b: t for t, b in enumerate(Bs[k])} for k in Bs}
deg = lambda b: 3 * b[1] + (b[3] - b[2]) if b[0] == 'e' else 3 * b[1]

def mat(b):
    M = np.zeros((3, 3), dtype=np.int64)
    if b[0] == 'e': M[b[2], b[3]] = 1
    else: M[b[2], b[2]] = 1; M[b[2] + 1, b[2] + 1] = -1
    return M

def bracket(b, c):
    """[b,c] as dict {basis elt: coeff} (degree deg b + deg c)."""
    k = deg(b) + deg(c)
    if k > K: return None
    X, Y = mat(b), mat(c)
    C = (X @ Y - Y @ X) % p
    n = b[1] + c[1]
    out = {}
    for i in range(3):
        for j in range(3):
            if i != j and C[i, j]: out[('e', n, i, j)] = int(C[i, j])
    d = [int(C[i, i]) for i in range(3)]
    # diag(d1,d2,d3), trace 0: = d1 h_0 + (d1+d2) h_1
    if (d[0] % p) or ((d[0] + d[1]) % p):
        if d[0] % p: out[('h', n, 0)] = d[0] % p
        if (d[0] + d[1]) % p: out[('h', n, 1)] = (d[0] + d[1]) % p
    return out

brc = {}
def br(b, c):
    key = (b, c)
    if key not in brc: brc[key] = bracket(b, c)
    return brc[key]

def rank_mod_p(rows, ncols):
    """rank over F_p of an iterator of dict-rows {col: val}."""
    piv = {}  # col -> row vector (np array) normalised
    rk = 0
    for r in rows:
        v = np.zeros(ncols, dtype=np.int64)
        for c, x in r.items(): v[c] = (v[c] + x) % p
        for c, pv in piv.items():
            if v[c]: v = (v - v[c] * pv) % p
        nz = np.nonzero(v)[0]
        if len(nz):
            c = nz[0]; v = (v * pow(int(v[c]), p - 2, p)) % p
            for c2 in list(piv):
                if piv[c2][c]: piv[c2] = (piv[c2] - piv[c2][c] * v) % p
            piv[c] = v; rk += 1
            if rk == ncols: break
    return rk

def graded_pieces(k, m):
    """ordered m-tuples of basis elts with strictly increasing (deg,index) and total degree k"""
    elts = [b for d in range(1, k) for b in Bs[d]]
    order = {b: t for t, b in enumerate(elts)}
    def rec(start, rem, left):
        if left == 1:
            for b in Bs.get(rem, []):
                if order.get(b, -1) >= start: yield (b,)
            return
        for t in range(start, len(elts)):
            b = elts[t]; d = deg(b)
            if d * left > rem + 0 and d > rem: break
            for rest in rec(t + 1, rem - d, left - 1): yield (b,) + rest
    return list(rec(0, k, m)), order

res = []
for k in range(2, K + 1):
    L2, order = graded_pieces(k, 2)
    L3, _ = graded_pieces(k, 3)
    i2 = {w: t for t, w in enumerate(L2)}
    def wedge(x, y):
        if order[x] < order[y]: return (x, y), 1
        return (y, x), -1
    rk2 = rank_mod_p(((lambda d: {idx[k][b]: c for b, c in d.items()})(br(x, y)) for x, y in L2), len(Bs[k]))
    def d3(t):
        x, y, z = t
        out = {}
        for (u, v, w, s) in ((x, y, z, 1), (x, z, y, -1), (y, z, x, 1)):
            for b, c in br(u, v).items():
                if b == w: continue  # b ^ b = 0 ; cannot happen with distinct? keep safe
                key, sg = wedge(b, w)
                col = i2[key]
                out[col] = (out.get(col, 0) + s * sg * c) % p
        return out
    rk3 = rank_mod_p((d3(t) for t in L3), len(L2))
    h2 = len(L2) - rk2 - rk3
    h1 = len(Bs[k]) - rk2
    res.append((k, len(Bs[k]), h1, h2))
    if h2 or h1:
        print(f"p={p} degree {k}: dim L_k={len(Bs[k])} H_1={h1} H_2={h2}  (dim Lambda2={len(L2)}, Lambda3={len(L3)})", flush=True)
print(f"p={p}: degrees <= {K} with H_2 != 0: {[(k, h) for k, _, _, h in res if h]}")
