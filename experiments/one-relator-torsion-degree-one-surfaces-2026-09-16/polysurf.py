#!/usr/bin/env python3
"""Degree-one w-polygonal surfaces and the shell condition (Sh_n).

Words are lists of nonzero ints: +g is generator g (1-based), -g its inverse.
A surface is given by m faces (each reading w, length L) and a side-pairing:
a fixed-point-free involution on the sides (f, j), 0 <= f < m, 0 <= j < L,
pairing only sides with the same generator.  The positive edge of side (f, j)
runs tail -> head, where for w_j = +g: tail = (f, j), head = (f, j+1) and for
w_j = -g: tail = (f, j+1), head = (f, j).  Pairing identifies tails with tails
and heads with heads (labels and orientations respected).

Checks (exact, finite):
  * immersion: at every vertex, at most one outgoing and one incoming edge per
    generator;
  * V, E = mL/2, chi(S) = V - E + m;
  * chi_orb(n) = V - E + m/n  (Euler characteristic of the n-cone orbifold);
  * condition (D): for every vertex u and every cyclic permutation s of w^{+-1},
    if u is periodic under the partial injection rho_s (u -> end of the path
    reading s), then (u, s) is a face corner;
  * t(u, s) for non-corners: the largest j >= 0 such that the path reading
    s^j x exists from u (x = first letter of s); infinite iff periodic.
    (Sh_n) holds iff n >= t(u, s) + 2 for all non-corners, so
    n0 = max(2, max t + 2) is the least n0 with (Sh_n) for all n >= n0
    ((Sh_n) is monotone in n: a path reading s^{n-1}x contains one reading
    s^{n-2}x).
"""
import sys
from itertools import product


class UF:
    def __init__(self):
        self.p = {}

    def find(self, x):
        self.p.setdefault(x, x)
        r = x
        while self.p[r] != r:
            r = self.p[r]
        while self.p[x] != r:
            self.p[x], x = r, self.p[x]
        return r

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra != rb:
            self.p[ra] = rb


def inv(word):
    return [-x for x in reversed(word)]


def rot(word, j):
    return word[j:] + word[:j]


def tail_head(w, f, j):
    L = len(w)
    if w[j] > 0:
        return (f, j), (f, (j + 1) % L)
    return (f, (j + 1) % L), (f, j)


def build(w, m, pairing):
    """pairing: dict side->side (involution). Returns surface data or None
    if not a valid immersion."""
    L = len(w)
    uf = UF()
    for f in range(m):
        for j in range(L):
            uf.find((f, j))
    for (f, j), (g, k) in pairing.items():
        assert abs(w[j]) == abs(w[k])
        t1, h1 = tail_head(w, f, j)
        t2, h2 = tail_head(w, g, k)
        uf.union(t1, t2)
        uf.union(h1, h2)
    verts = sorted({uf.find((f, j)) for f in range(m) for j in range(L)})
    vid = {v: i for i, v in enumerate(verts)}
    out = {}
    inn = {}
    edges = set()
    for (f, j), (g, k) in pairing.items():
        e = min((f, j), (g, k))
        if e in edges:
            continue
        edges.add(e)
        t, h = tail_head(w, *e)
        t, h = vid[uf.find(t)], vid[uf.find(h)]
        gen = abs(w[e[1]])
        if (t, gen) in out or (h, gen) in inn:
            return None
        out[(t, gen)] = h
        inn[(h, gen)] = t
    corner_vertex = {(f, j): vid[uf.find((f, j))] for f in range(m) for j in range(L)}
    return dict(w=w, m=m, L=L, V=len(verts), E=len(edges), out=out, inn=inn,
                cv=corner_vertex, pairing=pairing)


def step(S, u, x):
    if x > 0:
        return S['out'].get((u, x))
    return S['inn'].get((u, -x))


def read(S, u, word):
    for x in word:
        u = step(S, u, x)
        if u is None:
            return None
    return u


def corners(S):
    w, m, L = S['w'], S['m'], S['L']
    C = set()
    for f in range(m):
        for j in range(L):
            u = S['cv'][(f, j)]
            s = tuple(rot(w, j))
            C.add((u, s))
            C.add((u, tuple(inv(list(s)))))
    return C


def analyse(S):
    w, L, V = S['w'], S['L'], S['V']
    perms = set()
    for j in range(L):
        perms.add(tuple(rot(w, j)))
        perms.add(tuple(inv(rot(w, j))))
    C = corners(S)
    D_ok = True
    bad = []
    tmax = -1
    for u in range(V):
        for s in perms:
            if (u, s) in C:
                continue
            # t(u,s): largest j with s^j x readable
            v = u
            j = 0
            periodic = False
            while True:
                if step(S, v, s[0]) is None:
                    break  # s^j x not readable -> t = j-1
                v2 = read(S, v, list(s))
                if v2 is None:
                    j += 1  # s^j x readable, s^{j+1} not
                    break
                v = v2
                j += 1
                if v == u or j > V + 1:
                    periodic = True
                    break
            if periodic:
                D_ok = False
                bad.append((u, s))
                continue
            t = j - 1
            tmax = max(tmax, t)
    n0 = None if not D_ok else max(2, tmax + 2)
    return D_ok, n0, bad


def orientable(S):
    """Orientability: sides paired with opposite induced directions in the two
    faces iff consistent orientation.  Build a 2-colouring of faces: pairing
    (f,j)~(g,k) with same letter sign means the faces induce opposite
    boundary directions on the edge iff face orientations agree."""
    w, m = S['w'], S['m']
    col = {0: 0}
    stack = [0]
    adj = {}
    for (f, j), (g, k) in S['pairing'].items():
        same = (w[j] > 0) == (w[k] > 0)
        # both faces traverse the edge in the same direction iff same sign;
        # for a consistent orientation the traversal directions must be
        # opposite, so faces need opposite colours iff same.
        adj.setdefault(f, []).append((g, 1 if same else 0))
    while stack:
        f = stack.pop()
        for g, par in adj.get(f, []):
            c = col[f] ^ par
            if g not in col:
                col[g] = c
                stack.append(g)
            elif col[g] != c:
                return False
    return True


def syllables(w):
    L = len(w)
    return [j for j in range(L) if w[j] != w[(j + 1) % L]]


def kw_partial(w):
    """Kim-Wilton partial side-pairing on P, P' (faces 0, 1): (0,j)~(1,j+1)
    iff w_j == w_{j+1}.  Returns pairing dict and the list of unpaired sides."""
    L = len(w)
    pair = {}
    for j in range(L):
        if w[j] == w[(j + 1) % L]:
            a, b = (0, j), (1, (j + 1) % L)
            pair[a] = b
            pair[b] = a
    left = [(f, j) for f in range(2) for j in range(L) if (f, j) not in pair]
    return pair, left


def matchings(items, compatible):
    if not items:
        yield []
        return
    a = items[0]
    for i in range(1, len(items)):
        b = items[i]
        if compatible(a, b):
            rest = items[1:i] + items[i + 1:]
            for mm in matchings(rest, compatible):
                yield [(a, b)] + mm


def kw_completions(w):
    L = len(w)
    pair, left = kw_partial(w)
    comp = lambda a, b: abs(w[a[1]]) == abs(w[b[1]])
    for mm in matchings(left, comp):
        p = dict(pair)
        for a, b in mm:
            p[a] = b
            p[b] = a
        S = build(w, 2, p)
        if S is not None:
            yield S


def all_two_face(w, limit=None):
    """Exhaustive: all side-pairings of 2 faces reading w (same generator),
    immersion checked at the end (with incremental pruning via partial
    build on complete pairings only; fine for small L)."""
    L = len(w)
    sides = [(f, j) for f in range(2) for j in range(L)]
    comp = lambda a, b: abs(w[a[1]]) == abs(w[b[1]])
    cnt = 0
    for mm in matchings(sides, comp):
        p = {}
        for a, b in mm:
            p[a] = b
            p[b] = a
        S = build(w, 2, p)
        if S is not None:
            cnt += 1
            yield S
            if limit and cnt >= limit:
                return


def parse(s):
    """'aabbAAbb' style: lowercase = generator, uppercase = inverse."""
    return [(ord(c.lower()) - 96) * (1 if c.islower() else -1) for c in s]


def show(w):
    return ''.join(chr(96 + abs(x)) if x > 0 else chr(64 + abs(x)) for x in w)


def summary(S):
    D_ok, n0, bad = analyse(S)
    V, E, m = S['V'], S['E'], S['m']
    return dict(V=V, E=E, chi=V - E + m, orientable=orientable(S), D=D_ok,
                n0=n0, nbad=len(bad))


if __name__ == '__main__':
    for arg in sys.argv[1:]:
        w = parse(arg)
        print('word', arg, 'L', len(w))
        for S in kw_completions(w):
            print('  KW completion', summary(S))
