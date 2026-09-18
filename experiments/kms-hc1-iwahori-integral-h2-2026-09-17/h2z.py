#!/usr/bin/env python3
"""Integral H_1 and H_2 of the Chevalley Z-form of the pro-p Iwahori Lie algebra.

L_Z = n^+(sl_3)_Z + t sl_3(Z[t]), with Chevalley basis t^a E_ij (i != j) and
t^a h_1, t^a h_2 (h_1 = E11-E22, h_2 = E22-E33).  L_Z is graded by the affine
root lattice: wt(t^a E_ij) = eps_i - eps_j + a*delta, written in the simple
root coordinates (c0, c1, c2) with delta = (1,1,1).  The p-central degree of
L_p = L_Z (x) F_p is c0+c1+c2.

The Chevalley--Eilenberg complex splits by weight.  For each weight w we
compute, over Z,
  * H_1(L_Z)_w = coker(d_2 : Lambda^2_w -> L_w),
  * the torsion of H_2(L_Z)_w = torsion of coker(d_3 : Lambda^3_w -> Lambda^2_w)
    (Lambda^2/ker d_2 embeds in the free group L_w, so this is exact),
  * the free rank of H_2(L_Z)_w = dim ker d_2 - rank d_3.
By universal coefficients, when H_1(L_Z) is free (checked below),
  dim_{F_p} H_2(L_p)_w = rank H_2(L_Z)_w + #{elementary divisors of d_3 at w divisible by p}.

usage: h2z.py MAXDEG            (prints one line per weight with nonzero data,
                                 then a per-degree summary)
"""
import sys, itertools
from flint import fmpz_mat

K = int(sys.argv[1]) if len(sys.argv) > 1 else 30

# basis: (kind, i, j, a).  kind 'e' root vector t^a E_ij, kind 'h' t^a h_s with s=i (1 or 2)
def wt_root(i, j, a):
    # eps_i - eps_j in simple-root coordinates (c1, c2); alpha_0 = delta - (eps1-eps3)
    v = {(1, 2): (0, 1, 0), (2, 3): (0, 0, 1), (1, 3): (0, 1, 1),
         (2, 1): (0, -1, 0), (3, 2): (0, 0, -1), (3, 1): (0, -1, -1)}[(i, j)]
    return (v[0] + a, v[1] + a, v[2] + a)

basis = []
maxa = K // 3 + 2
for a in range(0, maxa + 1):
    for (i, j) in [(1, 2), (2, 3), (1, 3), (2, 1), (3, 2), (3, 1)]:
        if i > j and a == 0:
            continue
        w = wt_root(i, j, a)
        if sum(w) <= K:
            basis.append(('e', i, j, a, w))
    if a >= 1 and 3 * a <= K:
        basis.append(('h', 1, 0, a, (a, a, a)))
        basis.append(('h', 2, 0, a, (a, a, a)))
index = {}
for n, b in enumerate(basis):
    index[b[:4]] = n
byw = {}
for n, b in enumerate(basis):
    byw.setdefault(b[4], []).append(n)
W = [b[4] for b in basis]

def mat(b):
    """3x3 matrix of basis element as dict {(r,c):coef}, together with t-power."""
    kind, i, j, a, _ = b
    if kind == 'e':
        return {(i, j): 1}, a
    if i == 1:
        return {(1, 1): 1, (2, 2): -1}, a
    return {(2, 2): 1, (3, 3): -1}, a

def bracket(x, y):
    """[x,y] as dict {basis index: coef} (integral)."""
    X, a = mat(basis[x]); Y, b = mat(basis[y])
    C = {}
    for (r, s), u in X.items():
        for (s2, c), v in Y.items():
            if s == s2:
                C[(r, c)] = C.get((r, c), 0) + u * v
    for (r, s), u in Y.items():
        for (s2, c), v in X.items():
            if s == s2:
                C[(r, c)] = C.get((r, c), 0) - u * v
    n = a + b
    out = {}
    d = [C.get((k, k), 0) for k in (1, 2, 3)]
    # diagonal part d1 E11 + d2 E22 + d3 E33 with trace 0 = d1 h1 + (d1+d2) h2
    if any(d):
        assert sum(d) == 0
        if d[0]:
            out[index[('h', 1, 0, n)]] = d[0]
        if d[0] + d[1]:
            out[index[('h', 2, 0, n)]] = d[0] + d[1]
    for (r, c), v in C.items():
        if r != c and v:
            out[index[('e', r, c, n)]] = out.get(index[('e', r, c, n)], 0) + v
    return {k: v for k, v in out.items() if v}

def addw(u, v):
    return (u[0] + v[0], u[1] + v[1], u[2] + v[2])

def subw(u, v):
    return (u[0] - v[0], u[1] - v[1], u[2] - v[2])

deg = [sum(w) for w in W]
order = sorted(range(len(basis)), key=lambda n: deg[n])
PAIRS = {}
TRIPLES = {}
for x in range(len(basis)):
    for y in range(x + 1, len(basis)):
        if deg[x] + deg[y] > K:
            continue
        wxy = addw(W[x], W[y])
        PAIRS.setdefault(wxy, []).append((x, y))
        for z in range(y + 1, len(basis)):
            if deg[x] + deg[y] + deg[z] <= K:
                TRIPLES.setdefault(addw(wxy, W[z]), []).append((x, y, z))

def weights_upto(K):
    return sorted(PAIRS, key=lambda w: (sum(w), w))

def pairs_at(w):
    return PAIRS.get(w, [])

def triples_at(w):
    return TRIPLES.get(w, [])

def wedge2(x, y):
    """x^y as (sign, pair) with pair sorted, or None if x==y."""
    if x == y:
        return None
    return (1, (x, y)) if x < y else (-1, (y, x))

def smith_diag(rows):
    if not rows or not rows[0]:
        return []
    M = fmpz_mat(rows)
    H = M.hnf()
    # drop zero rows, then SNF of the (small) nonzero part
    nz = [r for r in H.tolist() if any(int(v) for v in r)]
    if not nz:
        return []
    S = fmpz_mat(nz).snf()
    return [abs(int(S[i, i])) for i in range(min(S.nrows(), S.ncols())) if int(S[i, i])]

def analyze(w):
    P = pairs_at(w)
    T = triples_at(w)
    Lw = byw.get(w, [])
    pidx = {pr: n for n, pr in enumerate(P)}
    # d2 : pair (x,y) -> -[x,y] ; rows = pairs (as generators), columns = L_w
    lidx = {b: n for n, b in enumerate(Lw)}
    d2rows = []
    for (x, y) in P:
        row = [0] * len(Lw)
        for k, v in bracket(x, y).items():
            row[lidx[k]] -= v
        d2rows.append(row)
    # d3 : (x,y,z) -> -[x,y]^z + [x,z]^y - [y,z]^x ; rows = triples, columns = pairs
    d3rows = []
    for (x, y, z) in T:
        row = [0] * len(P)
        for (u, v, s, c) in ((x, y, -1, z), (x, z, 1, y), (y, z, -1, x)):
            for k, co in bracket(u, v).items():
                wv = wedge2(k, c)
                if wv is None:
                    continue
                sg, pr = wv
                row[pidx[pr]] += s * sg * co
        if any(row):
            d3rows.append(row)
    e2 = smith_diag(d2rows) if Lw and d2rows else []
    rank2 = len(e2)
    h1_free = len(Lw) - rank2
    h1_tors = [e for e in e2 if e > 1]
    e3 = smith_diag(d3rows) if d3rows else []
    rank3 = len(e3)
    h2_free = (len(P) - rank2) - rank3
    h2_tors = [e for e in e3 if e > 1]
    return len(Lw), len(P), len(T), h1_free, h1_tors, h2_free, h2_tors

def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

if __name__ == '__main__':
    summary = {}
    for w in weights_upto(K):
        nL, nP, nT, h1f, h1t, h2f, h2t = analyze(w)
        k = sum(w)
        if h1f or h1t or h2f or h2t:
            print(f"deg {k:3d} wt {w}: L={nL} L2={nP} L3={nT}  H1 free {h1f} tors {h1t}  H2 free {h2f} tors {h2t}", flush=True)
        s = summary.setdefault(k, [0, 0, []])
        s[0] += h1f; s[1] += h2f; s[2] += h2t
    print("# per degree: H1 free rank, H2 free rank, H2 torsion invariants (factored)")
    for k in sorted(summary):
        h1f, h2f, tors = summary[k]
        ft = [factor(t) for t in tors]
        print(f"degree {k:3d}: H1 {h1f}  H2 free {h2f}  torsion {tors} {ft}", flush=True)
