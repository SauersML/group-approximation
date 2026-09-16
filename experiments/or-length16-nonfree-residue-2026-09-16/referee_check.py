#!/usr/bin/env python3
"""Referee's third checker (written from the claim statement only, not from recheck.py/verify.py).

For each CERT line: parse w, a=, t=, cp=.  Check (V0)-(V3) of
virtual-fibring-collapse-certificate-gives-rf-sofic, and additionally compute
dim H_1(X[0,S];F_p), dim H_2(X[0,S];F_p) as sanity (must be n and 0).
"""
import sys, re, random
from math import gcd

P = 1000003

def parse(line):
    toks = line.split()
    w = toks[1]
    def grab(key):
        m = re.search(r'\s%s=\[([-0-9, ]*)\]' % key, line)
        return [int(x) for x in m.group(1).replace(' ', '').split(',') if x != '']
    return w, grab('a'), grab('t'), grab('cp')

INV = {'a': 'A', 'A': 'a', 't': 'T', 'T': 't'}

def v0(w):
    if any(ch not in INV for ch in w):
        return False
    L = len(w)
    for i in range(L):
        if w[(i + 1) % L] == INV[w[i]]:
            return False
    if not (set('aA') & set(w)) or not (set('tT') & set(w)):
        return False
    for d in range(1, L):
        if L % d == 0 and w[:d] * (L // d) == w:
            return False
    return True

def boundary(w, a, t, cp, s):
    """Return list of (edge_id=(letter,i), orientation, tail_vertex_rel) and vertex list (i,h) along path."""
    k = len(a)
    perm = {'a': a, 't': t}
    inv = {x: [None] * k for x in 'at'}
    for x in 'at':
        for i, j in enumerate(perm[x]):
            inv[x][j] = i
    col = {'a': 0, 't': k}
    cur, h = s, 0
    path = [(cur, h)]
    edges = []
    for ch in w:
        x = ch.lower()
        if ch == x:
            e = (x, cur)
            c = cp[col[x] + cur]
            edges.append((e, h))          # tail height
            cur, h = perm[x][cur], h + c
        else:
            j = inv[x][cur]
            e = (x, j)
            c = cp[col[x] + j]
            edges.append((e, h - c))
            cur, h = j, h - c
        path.append((cur, h))
    return edges, path

def build(w, a, t, cp, lo, hi):
    k = len(a)
    perm = {'a': a, 't': t}
    col = {'a': 0, 't': k}
    V = set((i, y) for i in range(k) for y in range(lo, hi + 1))
    E = {}
    for x in 'at':
        for i in range(k):
            c = cp[col[x] + i]
            for y in range(lo, hi + 1):
                if lo <= y + c <= hi:
                    E[(x, i, y)] = ((i, y), (perm[x][i], y + c))
    F = {}
    for s in range(k):
        edges, path = boundary(w, a, t, cp, s)
        hs = [h for _, h in path]
        for y in range(lo - min(hs), hi - max(hs) + 1):
            F[(s, y)] = [(e[0], e[1], ty + y) for e, ty in edges]
    for f, bd in F.items():
        for e in bd:
            assert e in E, (f, e)
    return V, E, F

def try_collapse(big, small, order_rng):
    V, E, F = big
    v0_, e0, f0 = small
    aliveV, aliveE, aliveF = set(V), set(E), set(F)
    cells_of_edge = {e: [] for e in E}
    for f, bd in F.items():
        for e in bd:
            cells_of_edge[e].append(f)
    edges_at = {v: [] for v in V}
    for e, (u, x) in E.items():
        edges_at[u].append(e)
        edges_at[x].append(e)
    cells_at = {v: set() for v in V}
    for f, bd in F.items():
        for e in bd:
            for v in E[e]:
                cells_at[v].add(f)
    changed = True
    while changed:
        changed = False
        cand = [('v', v) for v in aliveV if v not in v0_] + [('e', e) for e in aliveE if e not in e0]
        if order_rng is None:
            cand.sort()
        else:
            order_rng.shuffle(cand)
        for kind, p in cand:
            if kind == 'v':
                if p not in aliveV:
                    continue
                inc = [e for e in edges_at[p] if e in aliveE]   # a loop appears twice
                if len(inc) != 1:
                    continue
                e = inc[0]
                if E[e][0] == E[e][1]:
                    continue
                if any(f in aliveF for f in cells_at[p]):
                    continue
                if e in e0:
                    continue
                aliveV.discard(p); aliveE.discard(e); changed = True
            else:
                if p not in aliveE:
                    continue
                occ = [f for f in cells_of_edge[p] if f in aliveF]  # with multiplicity
                if len(occ) != 1:
                    continue
                f = occ[0]
                if f in f0:
                    continue
                aliveE.discard(p); aliveF.discard(f); changed = True
    return aliveV == set(v0_) and aliveE == set(e0) and aliveF == set(f0)

def rank_mod_p(rows, ncols):
    # rows: list of dict col->val
    piv = {}
    r = 0
    for row in rows:
        row = {c: v % P for c, v in row.items() if v % P}
        while row:
            c = min(row)
            if c in piv:
                prow = piv[c]
                m = row[c]
                for cc, vv in prow.items():
                    row[cc] = (row.get(cc, 0) - m * vv) % P
                    if row[cc] == 0:
                        del row[cc]
            else:
                inv = pow(row[c], P - 2, P)
                row = {cc: vv * inv % P for cc, vv in row.items()}
                piv[c] = row
                r += 1
                break
    return r

def homology(cx):
    V, E, F = cx
    vi = {v: i for i, v in enumerate(sorted(V))}
    ei = {e: i for i, e in enumerate(sorted(E))}
    d1 = []
    for e, (u, x) in E.items():
        row = {}
        row[vi[x]] = row.get(vi[x], 0) + 1
        row[vi[u]] = row.get(vi[u], 0) - 1
        d1.append(row)
    d2 = []
    for f, bd in F.items():
        # orientation: need signs; recompute via word letters
        d2.append(bd)
    return vi, ei, d1

def check(line):
    w, a, t, cp = parse(line)
    k = len(a)
    if not v0(w):
        return w, 'FAIL V0'
    if sorted(a) != list(range(k)) or sorted(t) != list(range(k)) or len(cp) != 2 * k:
        return w, 'FAIL shape'
    # V1: relator fixes every point; transitivity
    for s in range(k):
        edges, path = boundary(w, a, t, cp, s)
        if path[-1][0] != s:
            return w, 'FAIL V1 relator'
        if path[-1][1] != 0:
            return w, 'FAIL V2 cocycle'
    seen = {0}
    frontier = [0]
    while frontier:
        i = frontier.pop()
        for j in (a[i], t[i], a.index(i), t.index(i)):
            if j not in seen:
                seen.add(j); frontier.append(j)
    if len(seen) != k:
        return w, 'FAIL V1 transitive'
    # V2 gcd: union-find spanning tree with potentials
    pot = {0: 0}
    queue = [0]
    tree_edges = []
    allE = [('a', i, a[i], cp[i]) for i in range(k)] + [('t', i, t[i], cp[k + i]) for i in range(k)]
    changed = True
    while changed:
        changed = False
        for x, i, j, c in allE:
            if i in pot and j not in pot:
                pot[j] = pot[i] + c; changed = True
            elif j in pot and i not in pot:
                pot[i] = pot[j] - c; changed = True
    g = 0
    for x, i, j, c in allE:
        g = gcd(g, pot[i] + c - pot[j])
    if g != 1:
        return w, 'FAIL V2 gcd %d' % g
    S = 0
    for s in range(k):
        _, path = boundary(w, a, t, cp, s)
        hs = [h for _, h in path]
        S = max(S, max(hs) - min(hs))
    if any(abs(c) > S for c in cp):
        return w, 'FAIL V3 edge span'
    mid = build(w, a, t, cp, 0, S)
    for lo, hi in ((0, S + 1), (-1, S)):
        big = build(w, a, t, cp, lo, hi)
        ok = try_collapse(big, mid, None)
        sd = 0
        while not ok and sd < 30:
            ok = try_collapse(big, mid, random.Random(1000 + sd)); sd += 1
        if not ok:
            return w, 'FAIL V3 collapse [%d,%d]' % (lo, hi)
    V, E, F = mid
    chi = len(V) - len(E) + len(F)
    # sanity homology over F_p: dims of H_1, H_2 of X[0,S]
    vi = {v: i for i, v in enumerate(sorted(V))}
    ei = {e: i for i, e in enumerate(sorted(E))}
    d1 = []
    for e, (u, x) in E.items():
        row = {}
        row[vi[x]] = row.get(vi[x], 0) + 1
        row[vi[u]] = row.get(vi[u], 0) - 1
        d1.append(row)
    d2 = []
    for (s, y) in F:
        edges, path = boundary(w, a, t, cp, s)
        row = {}
        for idx, ch in enumerate(w):
            e, ty = edges[idx]
            key = ei[(e[0], e[1], ty + y)]
            sg = 1 if ch.islower() else -1
            row[key] = row.get(key, 0) + sg
        d2.append(row)
    r1 = rank_mod_p(d1, len(V))
    r2 = rank_mod_p(d2, len(E))
    h0 = len(V) - r1
    h1 = len(E) - r1 - r2
    h2 = len(F) - r2
    n = 1 - chi
    tag = 'OK' if (h0 == 1 and h2 == 0 and h1 == n) else 'HOMOLOGY_MISMATCH'
    return w, 'REFOK k=%d S=%d n=%d h0=%d h1=%d h2=%d %s' % (k, S, n, h0, h1, h2, tag)

def main():
    cnt = 0
    for fn in sys.argv[1:]:
        for line in open(fn):
            if line.startswith('CERT'):
                w, v = check(line)
                print(w, v, flush=True)
                cnt += 1
    print('COUNT', cnt)

if __name__ == '__main__':
    main()
