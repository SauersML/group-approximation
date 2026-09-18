"""Permutation-pair toolkit: covers of square-tiled tori with non-abelian fibre,
exact rectangle profile, and exact one-sided rounding in any GL2(Z) frame.

Conventions: a permutation is a numpy int array p with p[i] = image of i.
comp(p,q) = p o q (q first).  rank(p - q) = n - #cycles(p q^-1).
"""
import numpy as np
from itertools import product
from scipy.optimize import linear_sum_assignment

def comp(p, q): return p[q]
def inv(p):
    r = np.empty_like(p); r[p] = np.arange(len(p)); return r
def ident(n): return np.arange(n)
def pw(p, e):
    n = len(p); r = ident(n); q = p if e >= 0 else inv(p); e = abs(e)
    while e:
        if e & 1: r = q[r]
        q = q[q]; e >>= 1
    return r
def cycles_of(p):
    n = len(p); seen = np.zeros(n, bool); out = []
    for i in range(n):
        if not seen[i]:
            cyc = []; j = i
            while not seen[j]:
                seen[j] = True; cyc.append(j); j = p[j]
            out.append(cyc)
    return out
def ncyc(p):
    n = len(p); seen = np.zeros(n, bool); k = 0
    for i in range(n):
        if not seen[i]:
            k += 1; j = i
            while not seen[j]:
                seen[j] = True; j = p[j]
    return k
def rk(p, q): return len(p) - ncyc(p[inv(q)])
def rkI(p): return len(p) - ncyc(p)
def order(p):
    from math import gcd
    o = 1
    for c in cycles_of(p):
        L = len(c); o = o * L // gcd(o, L)
    return o
def comm(p, q):  # p q p^-1 q^-1
    return comp(comp(p, q), comp(inv(p), inv(q)))

# ---------- groups (regular fibres) ----------
def group_from_gens(gens):
    """close a set of permutations (tuples) under composition; return (elements, mult table)."""
    gens = [tuple(g) for g in gens]; d = len(gens[0])
    e = tuple(range(d)); els = [e]; idx = {e: 0}; frontier = [e]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = tuple(g[x[i]] for i in range(d))
                if y not in idx: idx[y] = len(els); els.append(y); nf.append(y)
        frontier = nf
    m = len(els); mul = np.zeros((m, m), int)
    for i, x in enumerate(els):
        for j, y in enumerate(els):
            mul[i, j] = idx[tuple(x[y[k]] for k in range(d))]   # x o y
    return els, mul

def named_group(name):
    if name == 'S3': return group_from_gens([(1, 0, 2), (1, 2, 0)])
    if name == 'A4': return group_from_gens([(1, 2, 0, 3), (1, 0, 3, 2)])
    if name == 'Q8':  # regular rep via i, j acting on 8 points (quaternion units)
        # encode q = (sign, unit) unit in 1,i,j,k ; index = 2*unit + (sign<0)
        tab = {('1', '1'): (1, '1'), ('1', 'i'): (1, 'i'), ('1', 'j'): (1, 'j'), ('1', 'k'): (1, 'k'),
               ('i', '1'): (1, 'i'), ('i', 'i'): (-1, '1'), ('i', 'j'): (1, 'k'), ('i', 'k'): (-1, 'j'),
               ('j', '1'): (1, 'j'), ('j', 'i'): (-1, 'k'), ('j', 'j'): (-1, '1'), ('j', 'k'): (1, 'i'),
               ('k', '1'): (1, 'k'), ('k', 'i'): (1, 'j'), ('k', 'j'): (-1, 'i'), ('k', 'k'): (-1, '1')}
        U = '1ijk'
        def left(a):
            p = [0] * 8
            for u in range(4):
                for s in (0, 1):
                    sg, w = tab[(a, U[u])]
                    s2 = s ^ (sg < 0); p[2 * u + s] = 2 * U.index(w) + s2
            return tuple(p)
        return group_from_gens([left('i'), left('j')])
    if name.startswith('Z'):
        m = int(name[1:]); return group_from_gens([tuple((i + 1) % m for i in range(m))])
    if name.startswith('S'):
        m = int(name[1:]); return group_from_gens([tuple([1, 0] + list(range(2, m))), tuple(list(range(1, m)) + [0])])
    raise ValueError(name)

# ---------- base tori ----------
class Torus:
    """G = Z^2 / <(N1,0),(C,N2)>, element index y*N1 + x."""
    def __init__(s, N1, N2, C):
        s.N1, s.N2, s.C = N1, N2, C; s.N = N1 * N2
    def idx(s, x, y):
        q = y // s.N2; y -= q * s.N2; x -= q * s.C
        return y * s.N1 + (x % s.N1)
    def xy(s, h): return (h % s.N1, h // s.N1)
    def lam1(s):
        best = None
        for a in range(-s.N, s.N + 1):
            for b in range(-s.N, s.N + 1):
                if (a, b) != (0, 0) and s.idx(a, b) == 0:
                    v = abs(a) + abs(b)
                    if best is None or v < best[0]: best = (v, a, b)
        return best

def cover(T, mul, beta, gamma):
    """b(x,h) = (x+e1, beta(x) h), c(x,h) = (x+e2, gamma(x) h); point index x*m + h."""
    m = mul.shape[0]; n = T.N * m
    b = np.empty(n, int); c = np.empty(n, int)
    for x in range(T.N):
        X, Y = T.xy(x); xb = T.idx(X + 1, Y); xc = T.idx(X, Y + 1)
        for h in range(m):
            b[x * m + h] = xb * m + mul[beta[x], h]
            c[x * m + h] = xc * m + mul[gamma[x], h]
    return b, c

# ---------- profile ----------
def profile(b, c, smax=None, tmax=None):
    """exact sup_{s,t>=1} rank([b^s,c^t]-I)/(s+t) (periodicity: s <= ord b, t <= ord c)."""
    n = len(b); ob, oc = order(b), order(c)
    smax = ob if smax is None else min(smax, ob); tmax = oc if tmax is None else min(tmax, oc)
    best = (0.0, 0, 0); bs = ident(n)
    cts = [ident(n)]
    for t in range(1, tmax + 1): cts.append(comp(c, cts[-1]))
    for s in range(1, smax + 1):
        bs = comp(b, bs)
        if n / (s + 1) <= best[0]: break
        bsi = inv(bs)
        for t in range(1, tmax + 1):
            if n / (s + t) <= best[0]: break
            ct = cts[t]
            r = rkI(comp(comp(bs, ct), comp(bsi, inv(ct))))
            if r / (s + t) > best[0]: best = (r / (s + t), s, t)
    return best

# ---------- one-sided exact rounding ----------
def centralizer_round(X, Y):
    """Y' in C(X) maximizing #{Y' = Y} (exact: assignment per cycle length). Returns Y'."""
    n = len(X); cyc = cycles_of(X)
    cid = np.empty(n, int); pos = np.empty(n, int)
    for k, cy in enumerate(cyc):
        for i, x in enumerate(cy): cid[x] = k; pos[x] = i
    bylen = {}
    for k, cy in enumerate(cyc): bylen.setdefault(len(cy), []).append(k)
    Yp = np.empty(n, int)
    for L, ks in bylen.items():
        loc = {k: i for i, k in enumerate(ks)}
        cnt = {}
        for k in ks:
            for x in cyc[k]:
                y = Y[x]; k2 = cid[y]
                if len(cyc[k2]) == L:
                    key = (k, k2, (pos[y] - pos[x]) % L); cnt[key] = cnt.get(key, 0) + 1
        W = np.zeros((len(ks), len(ks))); R = {}
        for (k, k2, r), v in cnt.items():
            i, j = loc[k], loc[k2]
            if v > W[i, j]: W[i, j] = v; R[(i, j)] = r
        ri, ci = linear_sum_assignment(-W)
        for i, j in zip(ri, ci):
            k, k2 = ks[i], ks[j]; r = R.get((i, j), 0)
            for x in cyc[k]: Yp[x] = cyc[k2][(pos[x] + r) % L]
    return Yp

def frames(M):
    out = []
    for v1, v2, u1, u2 in product(range(-M, M + 1), repeat=4):
        if v1 * u2 - v2 * u1 == 1: out.append((v1, v2, u1, u2))
    return out

def word(b, c, e1, e2): return comp(pw(b, e1), pw(c, e2))   # b^e1 c^e2 (c first)

def round_in_frame(b, c, f):
    """keep B = b^v1 c^v2 (or C), round the other one in C(B), back-substitute."""
    v1, v2, u1, u2 = f
    B = word(b, c, v1, v2); C = word(b, c, u1, u2)
    res = []
    for keep in ('B', 'C'):
        if keep == 'B': Bn, Cn = B, centralizer_round(B, C)
        else: Cn, Bn = C, centralizer_round(C, B)
        bn = comp(pw(Bn, u2), pw(Cn, -v2)); cn = comp(pw(Bn, -u1), pw(Cn, v1))
        assert np.array_equal(comp(bn, cn), comp(cn, bn))
        res.append((max(rk(bn, b), rk(cn, c)), rk(bn, b), rk(cn, c), keep))
    return min(res)

def best_rounding(b, c, M=2):
    best = None
    for f in frames(M):
        r = round_in_frame(b, c, f)
        if best is None or r[0] < best[0][0]: best = (r, f)
    return best
