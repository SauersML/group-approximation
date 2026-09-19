#!/usr/bin/env python3
"""Exact check (rational arithmetic) that the pointed-forest window S_n embeds in the Cayley graph of F.

1. s0 = t+1 and s1 = (t<=0: t; [0,1]: 2t; t>=1: t+1) are PL maps of R.  We verify that
   u = s0, v = s1 satisfy the two defining relators of F,
       [u v^-1, u^-1 v u] = 1,   [u v^-1, u^-2 v u^2] = 1,
   with the product g*h := "first g, then h" (right action), and that u, v do not commute.  Every
   proper quotient of F is abelian (Cannon-Floyd-Parry, Thm 4.3), so x0 -> s0, x1 -> s1 is an
   isomorphism F -> <s0, s1>, and the Cayley graphs for {x0^+-1, x1^+-1} and {s0^+-1, s1^+-1} agree.
2. For every n <= NMAX: assign to each pointed forest with n leaves a group element by BFS from the
   all-leaves forest with pointer 0 (identity), along the forest moves of forest_window_scout.py.
   Verify that EVERY move edge (x, s, y) inside S_n satisfies elem(y) = elem(x) o s (composition of
   maps, s applied first), and that elem is injective on S_n.  Then S_n with its move edges is a
   subgraph of the right Cayley graph of (G, o), which is isomorphic (g -> g^-1) to the Cayley graph
   of (G, then) = F for the symmetric generating set {s0^+-1, s1^+-1}.  (With the other product,
   "elem(x) then s", the edges fail already at n = 4; see the note in the output.)
"""
import sys
from fractions import Fraction as Q
from collections import deque

sys.path.insert(0, '../thompson-f-cogrowth-2026-09-17')


class PL:
    """PL homeomorphism of R, slope 1 outside [xs[0], xs[-1]], given by breakpoints xs -> ys."""

    def __init__(self, xs, ys):
        pts = sorted(zip(xs, ys))
        # drop redundant breakpoints
        out = []
        for p in pts:
            if out and out[-1][0] == p[0]:
                continue
            out.append(p)
        clean = []
        for j, p in enumerate(out):
            if 0 < j < len(out) - 1:
                a, c = out[j - 1], out[j + 1]
                if (p[1] - a[1]) * (c[0] - p[0]) == (c[1] - p[1]) * (p[0] - a[0]):
                    continue
            clean.append(p)
        # slopes at the ends are 1; remove end points that are not breakpoints
        while len(clean) >= 2 and clean[1][1] - clean[0][1] == clean[1][0] - clean[0][0]:
            clean.pop(0)
        while len(clean) >= 2 and clean[-1][1] - clean[-2][1] == clean[-1][0] - clean[-2][0]:
            clean.pop()
        if len(clean) == 1:  # a translation: canonical representative point x = 0
            clean = [(Q(0), clean[0][1] - clean[0][0])]
        self.xs = tuple(p[0] for p in clean)
        self.ys = tuple(p[1] for p in clean)

    def __call__(self, t):
        xs, ys = self.xs, self.ys
        if t <= xs[0]:
            return ys[0] + (t - xs[0])
        if t >= xs[-1]:
            return ys[-1] + (t - xs[-1])
        for j in range(len(xs) - 1):
            if xs[j] <= t <= xs[j + 1]:
                return ys[j] + (ys[j + 1] - ys[j]) * (t - xs[j]) / (xs[j + 1] - xs[j])

    def inv(self):
        return PL(self.ys, self.xs)

    def then(self, h):  # first self, then h
        pts = set(self.xs) | {self.inv()(b) for b in h.xs}
        pts = sorted(pts)
        return PL(pts, [h(self(t)) for t in pts])

    def key(self):
        return (self.xs, self.ys)


s0 = PL([Q(0)], [Q(1)])
s1 = PL([Q(0), Q(1)], [Q(0), Q(2)])
ident = PL([Q(0)], [Q(0)])


def word(*gs):
    g = ident
    for h in gs:
        g = g.then(h)
    return g


def comm(a, b):
    return word(a, b, a.inv(), b.inv())


def check_relations():
    u, v = s0, s1
    a = word(u, v.inv())
    r1 = comm(a, word(u.inv(), v, u))
    r2 = comm(a, word(u.inv(), u.inv(), v, u, u))
    assert r1.key() == ident.key() and r2.key() == ident.key(), "relators fail"
    assert comm(u, v).key() != ident.key(), "commute"
    return True


def moves(state):
    f, i = state
    m = len(f)
    out = []
    if i + 1 < m:
        out.append((s0, (f, i + 1)))
        out.append((s1, (f[:i] + ((f[i], f[i + 1]),) + f[i + 2:], i)))
    if i > 0:
        out.append((s0.inv(), (f, i - 1)))
    if f[i] != ():
        out.append((s1.inv(), (f[:i] + (f[i][0], f[i][1]) + f[i + 1:], i)))
    return out


def check_window(n):
    from forest_window_scout import forests
    states = {(f, i) for f in forests(n) for i in range(len(f))}
    base = (tuple(() for _ in range(n)), 0)
    elem = {base: ident}
    dq = deque([base])
    while dq:
        x = dq.popleft()
        for g, y in moves(x):
            assert y in states
            if y not in elem:
                elem[y] = g.then(elem[x])  # elem(y) = elem(x) o g (composition of maps)
                dq.append(y)
    assert len(elem) == len(states), "window not connected"
    nedges = 0
    for x in states:
        for g, y in moves(x):
            assert elem[y].key() == g.then(elem[x]).key(), ("edge mismatch", x, y)
            nedges += 1
    keys = {elem[x].key() for x in states}
    assert len(keys) == len(states), "not injective"
    return len(states), nedges


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    print("relators of F hold, s0 s1 do not commute:", check_relations())
    for n in range(1, NMAX + 1):
        print("n=%d states=%d directed move edges=%d: all edges are Cayley edges, elem injective" %
              ((n,) + check_window(n)), flush=True)
