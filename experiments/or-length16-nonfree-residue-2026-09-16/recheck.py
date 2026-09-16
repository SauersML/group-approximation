#!/usr/bin/env python3
"""Second, independently written checker for virtual-fibring CERT lines (vfib.py format).

This file shares no code with research/artifacts/or-length15-residue-scripts/verify.py.  It reads
only the word w and the fields a=, t=, cp= of a CERT line and checks the hypotheses (V0)-(V3) of
virtual-fibring-collapse-certificate-gives-rf-sofic:

  (V0) w is cyclically reduced, uses both letters and is not a string repetition u^m, m >= 2;
  (V1) a, t are permutations of {0..k-1}, every point is fixed by the walk of w, and the action
       (lowercase letter x: i -> x[i], uppercase: i -> x^(-1)[i]) is transitive;
  (V2) the 1-cochain cp (a-edges 0..k-1, then t-edges) sums to 0 along the lift of w from every
       start point, and its values on the fundamental loops of a spanning tree have gcd 1;
  (V3) with S the largest height span of a cell lift, every edge has |cp| <= S (checked directly),
       and the finite subcomplexes X[0,S+1] and X[-1,S] of the infinite cyclic cover collapse onto
       X[0,S] by elementary collapses.  A vertex is collapsed only if it lies on exactly one alive
       edge, that edge is not a loop, and no alive 2-cell passes through the vertex (checked
       explicitly, not deduced from (V0)); an edge only if exactly one alive 2-cell contains it,
       exactly once.  Pieces of X[0,S] are never removed.
Greedy queue order first, then up to 50 seeded random orders.
Usage: recheck.py FILE...   (lines starting with CERT)
"""
import sys, re, random
from math import gcd


def fields(line):
    out = {}
    for key in ('a', 't', 'cp'):
        m = re.search(r'(?:^| )%s=\[([^\]]*)\]' % key, line)
        out[key] = [int(x) for x in m.group(1).split(',')]
    return line.split()[1], out


def proper_power(w):
    n = len(w)
    return any(n % d == 0 and w[:d] * (n // d) == w for d in range(1, n))


def cyc_reduced(w):
    return all(w[i].swapcase() != w[(i + 1) % len(w)] for i in range(len(w)))


class Cover:
    def __init__(self, w, a, t, cp):
        self.w, self.k = w, len(a)
        k = self.k
        self.fwd = {'a': list(a), 't': list(t)}
        self.bwd = {}
        for x in 'at':
            b = [None] * k
            for i, j in enumerate(self.fwd[x]):
                b[j] = i
            self.bwd[x] = b
        self.cp = {('a', i): cp[i] for i in range(k)}
        self.cp.update({('t', i): cp[k + i] for i in range(k)})

    def walk(self, s):
        """Lift of w from point s: list of (edge=(x,i), sign, start height) and final (point, height)."""
        p, h, steps = s, 0, []
        for ch in self.w:
            x = ch.lower()
            if ch == x:
                steps.append(((x, p), +1, h))
                h += self.cp[(x, p)]
                p = self.fwd[x][p]
            else:
                q = self.bwd[x][p]
                steps.append(((x, q), -1, h - self.cp[(x, q)]))
                h -= self.cp[(x, q)]
                p = q
        return steps, p, h


def window(C, lo, hi):
    """Pieces of the infinite cyclic cover with all vertex heights in [lo, hi]."""
    k = C.k
    verts = {(i, x) for i in range(k) for x in range(lo, hi + 1)}
    edges = {}
    for (x, i), c in C.cp.items():
        j = C.fwd[x][i]
        for y in range(lo, hi + 1):
            if lo <= y + c <= hi:
                edges[(x, i, y)] = ((i, y), (j, y + c))
    cells = {}
    for s in range(k):
        steps, _, _ = C.walk(s)
        rel = [(e[0], e[1], y0) for e, sg, y0 in steps]
        hts = []
        for (x, i), sg, y0 in steps:
            c = C.cp[(x, i)]
            hts += [y0, y0 + c]
        mn, mx = min(hts), max(hts)
        for y in range(lo - mn, hi - mx + 1):
            cells[(s, y)] = [(x, i, y0 + y) for (x, i, y0) in rel]
    return verts, edges, cells


def collapse(big, small, rng):
    verts, edges, cells = big
    tv, te, tc = small
    assert tv <= verts and set(te) <= set(edges) and set(tc) <= set(cells)
    av, ae, ac = set(verts), set(edges), set(cells)
    edge_cells = {e: {} for e in edges}          # edge -> {cell: multiplicity}
    vert_edges = {v: {} for v in verts}          # vertex -> {edge: multiplicity}
    vert_cells = {v: set() for v in verts}       # vertex -> cells through it
    for c, bd in cells.items():
        for e in bd:
            edge_cells[e][c] = edge_cells[e].get(c, 0) + 1
            for v in edges[e]:
                vert_cells[v].add(c)
    for e, (u, v) in edges.items():
        vert_edges[u][e] = vert_edges[u].get(e, 0) + 1
        vert_edges[v][e] = vert_edges[v].get(e, 0) + 1

    def free_pair(p):
        if p in av and p not in tv:
            inc = {e: m for e, m in vert_edges[p].items() if e in ae}
            if len(inc) == 1:
                (e, m), = inc.items()
                if m == 1 and e not in te and not any(c in ac for c in vert_cells[p]):
                    return ('v', p, e)
        if p in ae and p not in te:
            inc = {c: m for c, m in edge_cells[p].items() if c in ac}
            if len(inc) == 1:
                (c, m), = inc.items()
                if m == 1 and c not in tc:
                    return ('e', p, c)
        return None

    todo = list(av - tv) + list(ae - set(te))
    if rng is not None:
        rng.shuffle(todo)
    progress = True
    while progress:
        progress = False
        nxt = []
        for p in todo:
            fp = free_pair(p)
            if fp is None:
                if p in av or p in ae:
                    nxt.append(p)
                continue
            kind, f, q = fp
            if kind == 'v':
                av.discard(f); ae.discard(q)
            else:
                ae.discard(f); ac.discard(q)
            progress = True
        todo = nxt
        if rng is not None:
            rng.shuffle(todo)
    return av == tv and ae == set(te) and ac == set(tc)


def check(line):
    w, F = fields(line)
    a, t, cp = F['a'], F['t'], F['cp']
    k = len(a)
    if not (cyc_reduced(w) and set(w.lower()) == {'a', 't'} and not proper_power(w)):
        return w, 'REJECT word'
    if sorted(a) != list(range(k)) or sorted(t) != list(range(k)) or len(cp) != 2 * k:
        return w, 'REJECT perms'
    C = Cover(w, a, t, cp)
    for s in range(k):
        _, p, h = C.walk(s)
        if p != s:
            return w, 'REJECT relator'
        if h != 0:
            return w, 'REJECT cocycle'
    reach, stack = {0}, [0]
    while stack:
        i = stack.pop()
        for x in 'at':
            for j in (C.fwd[x][i], C.bwd[x][i]):
                if j not in reach:
                    reach.add(j); stack.append(j)
    if len(reach) != k:
        return w, 'REJECT transitive'
    ht, order = {0: 0}, [0]
    for i in order:
        for x in 'at':
            j = C.fwd[x][i]
            if j not in ht:
                ht[j] = ht[i] + C.cp[(x, i)]; order.append(j)
            j = C.bwd[x][i]
            if j not in ht:
                ht[j] = ht[i] - C.cp[(x, j)]; order.append(j)
    g = 0
    for (x, i), c in C.cp.items():
        g = gcd(g, ht[i] + c - ht[C.fwd[x][i]])
    if g != 1:
        return w, 'REJECT gcd=%d' % g
    spans = []
    for s in range(k):
        steps, _, _ = C.walk(s)
        hts = [y0 for _, _, y0 in steps] + [y0 + C.cp[e] for e, _, y0 in steps]
        spans.append(max(hts) - min(hts))
    S = max(spans)
    if max(abs(c) for c in C.cp.values()) > S:
        return w, 'REJECT edge-span'
    mid = window(C, 0, S)
    for lo, hi, tag in ((0, S + 1, 'top'), (-1, S, 'bottom')):
        big = window(C, lo, hi)
        ok = collapse(big, mid, None)
        seed = 0
        while not ok and seed < 50:
            ok = collapse(big, mid, random.Random(seed))
            seed += 1
        if not ok:
            return w, 'REJECT %s-collapse' % tag
    v, e, c = mid
    return w, 'RECHECKED k=%d S=%d chi(X[0,S])=%d' % (k, S, len(v) - len(e) + len(c))


def main():
    n = 0
    for path in sys.argv[1:]:
        for line in open(path):
            if line.startswith('CERT'):
                w, verdict = check(line)
                print('%s %s' % (w, verdict), flush=True)
                n += 1
    print('CHECKED %d' % n)
    print('SENTINEL_DONE', flush=True)


if __name__ == '__main__':
    main()
