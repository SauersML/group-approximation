#!/usr/bin/env python3
"""Surface-guided search for two-cell cores with class ratio a:b, ab != 0.

Glue two copies D0, D0' of the w-polygon and one copy D1 of the w^{-1}-polygon into a closed oriented
surface (random perfect matchings of letter occurrences, s paired with s^{-1}), push the gluing into
Gamma = fold(A u B) with D0, D0' -> A and D1 -> B, and record when the two w-cycles A, B stay distinct
lifts and have classes [u0] = a p, [u1] = b p with ab != 0, |a| != |b|.
Usage: search2.py MAXLEN NGEN SAMPLES SEED
"""
import sys, random
from search import words, fold, ratio

def gamma_classes(w, idents_edges):
    L = len(w)
    edges = []; path = [[], []]
    for c in range(2):
        for i, (g, s) in enumerate(w):
            v, nx = c * L + i, c * L + (i + 1) % L
            if s == 1: edges.append((v, nx, g)); path[c].append((len(edges) - 1, 1))
            else: edges.append((nx, v, g)); path[c].append((len(edges) - 1, -1))
    idents = []
    for (e1, e2) in idents_edges:
        a1, b1, _ = edges[e1]; a2, b2, _ = edges[e2]
        idents += [(a1, a2), (b1, b2)]
    uf, E = fold(2 * L, edges, idents)
    if uf.f(0) == uf.f(L): return None
    verts = sorted({uf.f(v) for v in range(2 * L)})
    elist = list(E.values()); eid = {(a, g): k for k, (a, b, g) in enumerate(elist)}
    adj = {v: [] for v in verts}
    for k, (a, b, g) in enumerate(elist):
        adj[a].append((b, k)); adj[b].append((a, k))
    root = verts[0]; seen = {root}; st = [root]; tree = set()
    while st:
        v = st.pop()
        for (x, k) in adj[v]:
            if x not in seen: seen.add(x); tree.add(k); st.append(x)
    if len(seen) != len(verts):
        return None
    nontree = [k for k in range(len(elist)) if k not in tree]
    col = {k: i for i, k in enumerate(nontree)}
    vecs = []
    for c in range(2):
        v = [0] * len(nontree)
        for (ei, s) in path[c]:
            a, b, g = edges[ei]; k = eid[(uf.f(a), g)]
            if k in col: v[col[k]] += s
        vecs.append(v)
    return len(nontree), vecs, len(verts), len(elist)

def main():
    maxlen, ngen, samples, seed = map(int, sys.argv[1:5])
    rng = random.Random(seed)
    ws = [w for w in words(maxlen, ngen) if len(w) == maxlen]
    print('#words', len(ws), flush=True)
    hits = {}
    for w in ws:
        L = len(w)
        # occurrences: (disc, pos). disc 0,1 -> A edges pos; disc 2 -> B edge pos (reads w^{-1}: letter inverse)
        for _ in range(samples):
            idents = []
            for g in range(ngen):
                pos = []; neg = []
                for d in range(3):
                    for i, (h, s) in enumerate(w):
                        if h != g: continue
                        sgn = s if d < 2 else -s
                        (pos if sgn == 1 else neg).append((d, i))
                rng.shuffle(neg)
                for (d1, i1), (d2, i2) in zip(pos, neg):
                    e1 = i1 if d1 < 2 else L + i1
                    e2 = i2 if d2 < 2 else L + i2
                    if e1 != e2: idents.append((e1, e2))
            res = gamma_classes(w, idents)
            if res is None: continue
            r, (v0, v1), nv, ne = res
            rt = ratio(v0, v1)
            if rt is None or rt[0] == 'zero': continue
            a, b = rt
            if a * b != 0 and abs(a) != abs(b):
                ws_ = ''.join(('xyz'[g] if s == 1 else 'XYZ'[g]) for g, s in w)
                key = (ws_, r, a, b)
                if key not in hits:
                    hits[key] = idents
                    print(ws_, 'rank', r, 'V', nv, 'E', ne, 'a,b', a, b, 'u0', v0, 'u1', v1, 'idents', idents, flush=True)
    print('#hits', len(hits))

if __name__ == '__main__':
    main()
