#!/usr/bin/env python3
"""Exact checks for thompson-f-one-sided-forest-windows-are-norm-lossless.

Model (as in thompson-f-norm-bound-from-forest-renewal-test-vector-proof): s0(t) = t+1,
s1(t) = t (t<=0), 2t ([0,1]), t+1 (t>=1); Cayley edges x -> x o g; E(S_n) the pointed-forest window.

  part 1  the intrinsic test in_R (conditions (a),(b),(c) of the proof) holds on every E(state),
          state in S_n, n <= NMAX; the two forbidden moves (pointer left at i = 0, split at a leaf)
          leave R; the move graph on S_n is the induced subgraph of the Cayley graph on E(S_n)
          (every neighbour x o g that lies in E(S_n) is the image of a move).
  part 2  absorption: for random finite sets A of words in s0, s1 (identity included) the explicit
          h of the proof (dyadic refinement, u^-1, shift) satisfies h o a in R for all a in A.
All arithmetic is exact (fractions).
"""
import random
import sys
from fractions import Fraction as Q
from collections import deque


class PL:
    """PL homeomorphism of R, slope 1 outside [xs[0], xs[-1]], breakpoints xs -> ys."""

    def __init__(self, xs, ys):
        pts = sorted(zip(xs, ys))
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
        while len(clean) >= 2 and clean[1][1] - clean[0][1] == clean[1][0] - clean[0][0]:
            clean.pop(0)
        while len(clean) >= 2 and clean[-1][1] - clean[-2][1] == clean[-1][0] - clean[-2][0]:
            clean.pop()
        if len(clean) == 1:
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

    def then(self, h):  # first self, then h  (= h o self)
        pts = sorted(set(self.xs) | {self.inv()(b) for b in h.xs})
        return PL(pts, [h(self(t)) for t in pts])

    def key(self):
        return (self.xs, self.ys)


s0 = PL([Q(0)], [Q(1)])
s1 = PL([Q(0), Q(1)], [Q(0), Q(2)])
ident = PL([Q(0)], [Q(0)])
GENS = [s0, s0.inv(), s1, s1.inv()]


def floor_q(x):
    return x.numerator // x.denominator


def std_dyadic(p, q):
    """[p, q] is a standard dyadic interval of length <= 1."""
    L = q - p
    if L <= 0 or L > 1 or L.numerator != 1 or (L.denominator & (L.denominator - 1)):
        return False
    return (p / L).denominator == 1


def cond_a(g):
    """(a): g^-1 maps every unit interval [b, b+1] linearly onto a standard dyadic interval of
    length <= 1.  Equivalently g maps Z into Z and is a translated tree map h_T on each [k, k+1]."""
    gi = g.inv()
    lo = floor_q(min(gi.xs)) - 1
    hi = floor_q(max(gi.xs)) + 1
    bps = set(gi.xs)
    for b in range(lo, hi + 1):
        if any(b < x < b + 1 for x in bps):
            return False
        if not std_dyadic(gi(Q(b)), gi(Q(b + 1))):
            return False
    return True


def in_R(g):
    """(a), (b) g(0) >= 0, (c) every k with g(k) < 0 has g(k+1) = g(k) + 1."""
    if not cond_a(g) or g(Q(0)) < 0:
        return False
    lo = floor_q(min(g.xs)) - 1
    for k in range(lo, 1):
        if g(Q(k)) < 0 and g(Q(k + 1)) != g(Q(k)) + 1:
            return False
    return True


def trees(n, memo={}):
    if n == 1:
        return [()]
    if n not in memo:
        memo[n] = [(l, r) for a in range(1, n) for l in trees(a) for r in trees(n - a)]
    return memo[n]


def forests(n):
    if n == 0:
        return [()]
    return [(t,) + rest for a in range(1, n + 1) for t in trees(a) for rest in forests(n - a)]


def moves(state):
    f, i = state
    m = len(f)
    out = []
    if i + 1 < m:
        out.append((0, (f, i + 1)))
        out.append((2, (f[:i] + ((f[i], f[i + 1]),) + f[i + 2:], i)))
    if i > 0:
        out.append((1, (f, i - 1)))
    if f[i] != ():
        out.append((3, (f[:i] + (f[i][0], f[i][1]) + f[i + 1:], i)))
    return out


def window_elements(n):
    states = [(f, i) for f in forests(n) for i in range(len(f))]
    base = (tuple(() for _ in range(n)), 0)
    elem = {base: ident}
    dq = deque([base])
    while dq:
        x = dq.popleft()
        for gi, y in moves(x):
            if y not in elem:
                elem[y] = GENS[gi].then(elem[x])  # E(y) = E(x) o g
                dq.append(y)
    assert len(elem) == len(states)
    return elem


def part1(nmax):
    for n in range(1, nmax + 1):
        elem = window_elements(n)
        keys = {e.key(): s for s, e in elem.items()}
        assert len(keys) == len(elem)
        n_forbidden = 0
        n_edges = 0
        for s, e in elem.items():
            assert in_R(e), ("E(state) not in R", s)
            mv = {gi: y for gi, y in moves(s)}
            f, i = s
            for gi in range(4):
                nb = GENS[gi].then(e)  # e o g
                if gi == 1 and i == 0 or gi == 3 and f[i] == ():
                    assert not in_R(nb), ("forbidden move stays in R", s, gi)
                    n_forbidden += 1
                if nb.key() in keys:  # a Cayley neighbour inside E(S_n) ...
                    assert gi in mv and keys[nb.key()] == mv[gi], ("extra edge", s, gi)
                    n_edges += 1
                if gi in mv:          # ... and every move is such a neighbour
                    assert nb.key() in keys
        print("part1 n=%d states=%d induced directed edges=%d = move edges; "
              "forbidden moves leaving R: %d" % (n, len(elem), n_edges, n_forbidden), flush=True)


def good_piece(p, q, invs):
    """Every a^-1 is linear on [p, q] and maps it onto a standard dyadic interval of length <= 1."""
    for ai in invs:
        if any(p < x < q for x in ai.xs):
            return False
        if not std_dyadic(ai(p), ai(q)):
            return False
    return True


def absorber(A):
    """The h of the proof: h o a in R for every a in A."""
    invs = [a.inv() for a in A]
    allx = [x for ai in invs for x in ai.xs]
    lo, hi = floor_q(min(allx)) - 1, floor_q(max(allx)) + 2
    pieces = []
    stack = [(Q(k), Q(k + 1)) for k in range(hi - 1, lo - 1, -1)]
    while stack:  # dyadic refinement, left to right
        p, q = stack.pop()
        if good_piece(p, q, invs):
            pieces.append((p, q))
        else:
            m = (p + q) / 2
            stack.append((m, q))
            stack.append((p, m))
    ends = [p for p, _ in pieces] + [pieces[-1][1]]
    j0 = ends.index(Q(0))
    u_inv = PL(ends, [Q(j - j0) for j in range(len(ends))])  # u maps [j, j+1] onto piece j
    for a in A:
        assert cond_a(a.then(u_inv)), "u^-1 o a fails (a)"
    C = 0
    while not all(in_R(a.then(u_inv).then(PL([Q(0)], [Q(C)]))) for a in A):
        C += 1  # the proof gives an explicit C; the loop just finds the least one
    return u_inv.then(PL([Q(0)], [Q(C)])), len(pieces), C


def random_word(L, rng):
    g = ident
    for _ in range(L):
        g = g.then(GENS[rng.randrange(4)])
    return g


def part2(trials, size, maxlen, seed):
    rng = random.Random(seed)
    for t in range(trials):
        A = [ident] + [random_word(rng.randint(1, maxlen), rng) for _ in range(size)]
        h, npieces, C = absorber(A)
        assert all(in_R(a.then(h)) for a in A)
        assert in_R(h)
        if t < 5 or t == trials - 1:
            print("part2 trial %d: |A|=%d, pieces=%d, shift C=%d, h o A inside R" %
                  (t, len(A), npieces, C), flush=True)
    print("part2: %d random sets absorbed" % trials)


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    part1(NMAX)
    part2(200, 12, 14, 20260917)
