#!/usr/bin/env python3
"""Search for two-w-cycle folded graphs whose w-cycle classes are dependent with ratio a:b, ab != 0.

Gamma = fold(circle_w  u  circle_w  /  k vertex identifications).  The two cycles are the images of
the circles (lifts of the w-cell at the images of the two base points).  We record (w, identifications,
rank, a, b, eps) whenever [u_0] = a p, [u_1] = b p in H_1(Gamma), gcd(a,b)=1, ab != 0, and the base
points stay distinct (two distinct lifts).  eps: both cells read w with the same orientation (+1).
Usage: search.py MAXLEN K NGEN
"""
import sys, itertools
from math import gcd

def words(maxlen, ngen):
    letters = [(g, s) for g in range(ngen) for s in (1, -1)]
    out = []
    def rec(w):
        if len(w) >= 2 and len(w) % 2 == 0:
            if w[0] != (w[-1][0], -w[-1][1]):
                out.append(tuple(w))
        if len(w) == maxlen:
            return
        for l in letters:
            if w and l == (w[-1][0], -w[-1][1]):
                continue
            rec(w + [l])
    rec([])
    res = []
    seen = set()
    for w in out:
        # exponent sums zero
        if any(sum(s for g, s in w if g == h) for h in range(ngen)):
            continue
        L = len(w)
        # not proper power
        if any(L % d == 0 and w == w[d:] + w[:d] for d in range(1, L)):
            continue
        # canonical up to rotation and inversion
        inv = tuple((g, -s) for g, s in reversed(w))
        cands = [w[i:] + w[:i] for i in range(L)] + [inv[i:] + inv[:i] for i in range(L)]
        c = min(cands)
        if c in seen:
            continue
        seen.add(c)
        # require all generators used
        if len({g for g, s in w}) < ngen:
            continue
        res.append(w)
    return res

class UF:
    def __init__(s, n): s.p = list(range(n))
    def f(s, x):
        while s.p[x] != x:
            s.p[x] = s.p[s.p[x]]; x = s.p[x]
        return x
    def u(s, a, b):
        a, b = s.f(a), s.f(b)
        if a != b: s.p[a] = b; return True
        return False

def fold(nv, edges, idents):
    """edges: list of (src,dst,gen) with gen>=0 (direction = positive letter). returns uf, edge map."""
    uf = UF(nv)
    for a, b in idents:
        uf.u(a, b)
    changed = True
    while changed:
        changed = False
        out = {}; inn = {}
        for (a, b, g) in edges:
            A, B = uf.f(a), uf.f(b)
            if (A, g) in out:
                if uf.u(out[(A, g)], B): changed = True
            else:
                out[(A, g)] = B
            if (B, g) in inn:
                if uf.u(inn[(B, g)], A): changed = True
            else:
                inn[(B, g)] = A
    # canonical edge set
    E = {}
    for idx, (a, b, g) in enumerate(edges):
        A, B = uf.f(a), uf.f(b)
        E.setdefault((A, g), (A, B, g))
    return uf, E

def classes(w, idents):
    L = len(w)
    edges = []
    path = [[], []]
    for c in range(2):
        for i, (g, s) in enumerate(w):
            v, nx = c * L + i, c * L + (i + 1) % L
            if s == 1:
                edges.append((v, nx, g)); path[c].append((len(edges) - 1, 1))
            else:
                edges.append((nx, v, g)); path[c].append((len(edges) - 1, -1))
    uf, E = fold(2 * L, edges, idents)
    if uf.f(0) == uf.f(L):
        return None
    verts = sorted({uf.f(v) for v in range(2 * L)})
    elist = list(E.values())
    eid = {(a, g): k for k, (a, b, g) in enumerate(elist)}
    # spanning tree
    adj = {v: [] for v in verts}
    for k, (a, b, g) in enumerate(elist):
        adj[a].append((b, k)); adj[b].append((a, k))
    root = verts[0]; seen = {root}; stack = [root]; tree = set()
    while stack:
        v = stack.pop()
        for (x, k) in adj[v]:
            if x not in seen:
                seen.add(x); tree.add(k); stack.append(x)
    if len(seen) != len(verts):
        return None
    nontree = [k for k in range(len(elist)) if k not in tree]
    col = {k: i for i, k in enumerate(nontree)}
    r = len(nontree)
    vecs = []
    for c in range(2):
        v = [0] * r
        for (ei, s) in path[c]:
            a, b, g = edges[ei]
            k = eid[(uf.f(a), g)]
            if k in col:
                v[col[k]] += s
        vecs.append(v)
    return r, vecs

def content(v):
    c = 0
    for x in v: c = gcd(c, abs(x))
    return c

def ratio(v0, v1):
    # returns (a,b) with v0 = a p, v1 = b p, gcd(a,b)=1, or None if independent
    r = len(v0)
    for i in range(r):
        for j in range(i + 1, r):
            if v0[i] * v1[j] - v0[j] * v1[i] != 0:
                return None
    c0, c1 = content(v0), content(v1)
    if c0 == 0 or c1 == 0:
        return ('zero', c0, c1)
    # p primitive with v0 = a p
    p = [x // c0 for x in v0]
    # sign of v1 relative to p
    k = next(i for i in range(r) if p[i] != 0)
    b = v1[k] // p[k]
    return (c0, b)

def main():
    maxlen, K, ngen = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    ws = words(maxlen, ngen)
    print('#words', len(ws), flush=True)
    hits = 0
    for w in ws:
        L = len(w)
        pairs = [(i, L + j) for i in range(L) for j in range(L)]
        found = set()
        for k in range(1, K + 1):
            for idents in itertools.combinations(pairs, k):
                res = classes(w, idents)
                if res is None: continue
                r, (v0, v1) = res
                rt = ratio(v0, v1)
                if rt is None or rt[0] == 'zero': continue
                a, b = rt
                if a * b != 0 and abs(a) != abs(b):
                    key = (r, a, b)
                    if key in found: continue
                    found.add(key); hits += 1
                    ws_ = ''.join(('xyz'[g] if s == 1 else 'XYZ'[g]) for g, s in w)
                    print(ws_, 'idents', idents, 'rank', r, 'a,b', a, b, 'u0', v0, 'u1', v1, flush=True)
    print('#hits', hits)

if __name__ == '__main__':
    main()
