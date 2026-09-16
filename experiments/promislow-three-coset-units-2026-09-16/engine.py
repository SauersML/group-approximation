#!/usr/bin/env python3
"""Minimal exact engine for R[P], P the Promislow (Hantzsche-Wendt) group.

Model (Gardam, arXiv:2312.05240, as in research/artifacts/promislow-reduced-norm-cp.py):
  a: v -> diag(1,-1,-1) v + (1,1,0),  b: v -> diag(-1,1,-1) v + (0,1,1).
x = a^2 = transl(2,0,0), y = b^2 = transl(0,2,0), z = (ab)^2 = transl(0,0,-2).
Element: dict {(c, (i,j,k)): coeff} meaning coeff * x^i y^j z^k * rep_c, c in 'eABC',
rep_e = 1, rep_A = a, rep_B = b, rep_C = ab.  Coefficients: python ints (optionally reduced mod n).
"""
from itertools import permutations
from collections import defaultdict

SIGN = {'e': (1, 1, 1), 'A': (1, -1, -1), 'B': (-1, 1, -1), 'C': (-1, -1, 1)}
K4 = 'eABC'
def k4mul(g, h):
    s = tuple(SIGN[g][i] * SIGN[h][i] for i in range(3))
    return next(k for k, v in SIGN.items() if v == s)
def amul(g, h):
    (s, t), (s2, t2) = g, h
    return (tuple(s[i] * s2[i] for i in range(3)), tuple(t[i] + s[i] * t2[i] for i in range(3)))
def ainv(g):
    s, t = g
    return (s, tuple(-s[i] * t[i] for i in range(3)))
E = ((1, 1, 1), (0, 0, 0))
a_ = ((1, -1, -1), (1, 1, 0))
b_ = ((-1, 1, -1), (0, 1, 1))
REP = {'e': E, 'A': a_, 'B': b_, 'C': amul(a_, b_)}
def word(*gs):
    r = E
    for g in gs:
        r = amul(r, g)
    return r
assert word(ainv(b_), a_, a_, b_, a_, a_) == E
assert word(ainv(a_), b_, b_, a_, b_, b_) == E
def lat_exp(t):
    assert all(v % 2 == 0 for v in t)
    return (t[0] // 2, t[1] // 2, -t[2] // 2)
def exp_to_transl(m):
    return (2 * m[0], 2 * m[1], -2 * m[2])
def decompose(g):
    s, t = g
    c = next(k for k, v in SIGN.items() if v == s)
    tau = tuple(t[i] - REP[c][1][i] for i in range(3))
    assert amul((E[0], tau), REP[c]) == g
    return lat_exp(tau), c
COC = {}
for c in K4:
    for d in K4:
        m, cd = decompose(amul(REP[c], REP[d]))
        assert cd == k4mul(c, d)
        COC[(c, d)] = m
def act(c, m):
    s = SIGN[c]
    return (s[0] * m[0], s[1] * m[1], s[2] * m[2])
# conjugation check: rep_c x^m rep_c^-1 = x^{act(c,m)}
for c in K4:
    for m in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
        g = word(REP[c], (E[0], exp_to_transl(m)), ainv(REP[c]))
        assert g[0] == E[0] and lat_exp(g[1]) == act(c, m)

def addm(m, n):
    return (m[0] + n[0], m[1] + n[1], m[2] + n[2])
def gmul(u, v, mod=None):
    out = defaultdict(int)
    for (c, m1), x1 in u.items():
        for (d, m2), x2 in v.items():
            out[(k4mul(c, d), addm(addm(m1, act(c, m2)), COC[(c, d)]))] += x1 * x2
    if mod:
        return {k: w % mod for k, w in out.items() if w % mod}
    return {k: w for k, w in out.items() if w}
ONE = {('e', (0, 0, 0)): 1}

# commutative Laurent polys: dict {(i,j,k): coeff}
def padd(p, q, mod=None):
    out = defaultdict(int)
    for k, w in p.items(): out[k] += w
    for k, w in q.items(): out[k] += w
    return {k: w % mod if mod else w for k, w in out.items() if (w % mod if mod else w)}
def pmul(p, q, mod=None):
    out = defaultdict(int)
    for m1, x1 in p.items():
        for m2, x2 in q.items():
            out[addm(m1, m2)] += x1 * x2
    return {k: w % mod if mod else w for k, w in out.items() if (w % mod if mod else w)}
def ptw(c, p):
    return {act(c, m): w for m, w in p.items()}
def pscale(p, s, mod=None):
    return {k: (w * s) % mod if mod else w * s for k, w in p.items() if ((w * s) % mod if mod else w * s)}

def components(u):
    comp = {c: {} for c in K4}
    for (c, m), w in u.items():
        comp[c][m] = w
    return comp
def assemble(p, q, r, s=None):
    u = {}
    for c, f in zip(K4, (p, q, r, s or {})):
        for m, w in f.items():
            if w:
                u[(c, m)] = w
    return u

def det_right_mult(u, mod=None):
    """det of w -> w u as left R[L]-linear map on basis (1,a,b,ab); matrix row c = c*u."""
    idx = {c: i for i, c in enumerate(K4)}
    M = [[{} for _ in range(4)] for _ in range(4)]
    for c in K4:
        prod = gmul({(c, (0, 0, 0)): 1}, u, mod)
        for (d, m), w in prod.items():
            M[idx[c]][idx[d]][m] = w
    D = {}
    for perm in permutations(range(4)):
        sgn = 1
        for i in range(4):
            for j in range(i + 1, 4):
                if perm[i] > perm[j]:
                    sgn = -sgn
        t = {(0, 0, 0): sgn}
        for i in range(4):
            t = pmul(t, M[i][perm[i]], mod)
            if not t:
                break
        D = padd(D, t, mod)
    return D

def nrd3(p, q, r, mod=None):
    """9-term reduced norm for s = 0 (from the verbatim 24-term list with s = 0)."""
    X, Xi, Y, Yi, Z, Zi = [{m: 1} for m in [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]]
    def T(*fs):
        t = {(0, 0, 0): 1}
        for f in fs:
            t = pmul(t, f, mod)
        return t
    A, B, C = (lambda f: ptw('A', f)), (lambda f: ptw('B', f)), (lambda f: ptw('C', f))
    terms = [
        (+1, T(A(p), B(p), C(p), p)),
        (-1, T(A(p), C(p), B(r), r, Y)),
        (-1, T(A(p), p, B(q), C(q), Xi)),
        (-1, T(B(p), C(p), A(q), q, X)),
        (-1, T(B(p), p, A(r), C(r), Yi)),
        (+1, T(A(q), B(q), C(q), q)),
        (-1, T(A(q), B(q), C(r), r, Zi)),
        (-1, T(C(q), q, A(r), B(r), Z)),
        (+1, T(A(r), B(r), C(r), r)),
    ]
    D = {}
    for s, t in terms:
        D = padd(D, pscale(t, s, mod), mod)
    return D
