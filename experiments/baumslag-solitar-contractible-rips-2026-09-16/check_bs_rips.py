#!/usr/bin/env python3
"""Verify the staircase generating set of BS(m,n) = <a,t | t a^m t^-1 = a^n>.

For every monotone lattice path P from (0,0) to (m,|n|), with d = sign(n):
  T = { s(r,i) = a^(-d i) t a^r : (r,i) in P },  S = {a,a^-1} u T u T^-1.
Checks, with the HNN normal form (Britton) as word problem solver:
  (1) |S| = 2 + 2(m+|n|): labels distinct except s(0,0) = s(m,|n|) = t;
  (2) every triangle of Cay(G,S) through 1 contains an edge labelled a^{+-1};
  (3) the common neighbours of 1 and a are exactly the third vertices of the
      triangles of the triangulated relator 2-cells containing the edge {1,a},
      m of them below (t-exponent -1) and |n| above (t-exponent +1);
  (4) no two common neighbours of 1 and a are adjacent (no 4-cliques);
  (5) 3(m+|n|) triangles through 1 (m+|n| free orbits, 3 vertices each).
Also cross-checks the normal form against the faithful affine representation
of BS(1,n), |n| >= 2, on random words.  Single-threaded, deterministic.
"""
import itertools, random, sys
from fractions import Fraction


class BS:
    def __init__(self, m, n):
        assert m >= 1 and n != 0
        self.m, self.n = m, n

    def mul_gen(self, g, x, e=1):
        # g = (c, ((eps1,r1),...)) meaning a^c t^eps1 a^r1 ... ; x in 'a','t'
        c, lst = g[0], list(g[1])
        if x == 't':
            for _ in range(abs(e)):
                s = 1 if e > 0 else -1
                if lst and lst[-1][0] == -s and lst[-1][1] == 0:
                    lst.pop()
                else:
                    lst.append((s, 0))
            return (c, tuple(lst))
        # multiply by a^e and carry leftwards
        carry = e
        j = len(lst) - 1
        while j >= 0 and carry != 0:
            s, r = lst[j]
            x_ = r + carry
            if s == 1:
                q, rr = divmod(x_, self.m)
                carry = self.n * q          # t a^(mq) = a^(nq) t
            else:
                q, rr = divmod(x_, abs(self.n))
                q = q if self.n > 0 else -q  # a^(x_) = a^(n q) a^rr
                carry = self.m * q          # t^-1 a^(nq) = a^(mq) t^-1
            lst[j] = (s, rr)
            j -= 1
        if j < 0:
            c += carry
        return (c, tuple(lst))

    def word(self, w):  # w: list of (letter, exponent)
        g = (0, ())
        for x, e in w:
            g = self.mul_gen(g, x, e)
        return g

    def inv_word(self, w):
        return [(x, -e) for x, e in reversed(w)]

    def to_word(self, g):
        w = [('a', g[0])]
        for s, r in g[1]:
            w += [('t', s), ('a', r)]
        return w

    def mul(self, g, h):
        for x, e in self.to_word(h):
            if e:
                g = self.mul_gen(g, x, e)
        return g

    def inv(self, g):
        return self.word(self.inv_word(self.to_word(g)))


def paths(m, n):
    for hs in itertools.combinations(range(m + n), m):
        P, r, i = [(0, 0)], 0, 0
        for k in range(m + n):
            if k in hs: r += 1
            else: i += 1
            P.append((r, i))
        yield P


def check(m, n, P):
    G, N, d = BS(m, n), abs(n), (1 if n > 0 else -1)
    one, A = G.word([]), G.word([('a', 1)])
    s = {p: G.word([('a', -d * p[1]), ('t', 1), ('a', p[0])]) for p in P}
    T = set(s.values())
    S = {A, G.inv(A)} | T | {G.inv(u) for u in T}
    assert len(S) == 2 + 2 * (m + N), ('labels', m, n, P, len(S))
    Sl = list(S)
    tri = 0
    for x, y in itertools.combinations(Sl, 2):
        z = G.mul(G.inv(x), y)
        if z in S:
            tri += 1
            assert A in (x, y, z) or G.inv(A) in (x, y, z), ('no a-edge', m, n, P)
    assert tri == 3 * (m + N), ('triangle count', m, n, P, tri)
    common = {k for k in Sl if G.mul(G.inv(A), k) in S}
    # third vertices from the triangulated 2-cells
    expect_below, expect_above = set(), set()
    for (r, i), (r2, i2) in zip(P, P[1:]):
        if r2 == r + 1:   # triangle {g0 t a^r, g0 t a^(r+1), g0 a^(d i)}
            g0 = G.word([('a', -r), ('t', -1)])
            expect_below.add(G.mul(g0, G.word([('a', d * i)])))
        else:             # triangle {g0 a^(d i), g0 a^(d i2), g0 t a^r}
            e = min(d * i, d * i2)   # the a-edge is {g0 a^e, g0 a^(e+1)}
            g0 = G.word([('a', -e)])
            expect_above.add(G.mul(g0, G.word([('t', 1), ('a', r)])))
    assert len(expect_below) == m and len(expect_above) == N
    assert common == expect_below | expect_above, ('cliques != cells', m, n, P)
    for k, l in itertools.combinations(common, 2):
        assert G.mul(G.inv(k), l) not in S, ('4-clique', m, n, P)
    return tri


def crosscheck(n, trials=300, rng=random.Random(1)):
    G = BS(1, n)
    mats = {'a': lambda e: (Fraction(1), Fraction(e)),
            't': lambda e: (Fraction(n) ** e, Fraction(0))}
    for _ in range(trials):
        w = [(rng.choice('at'), rng.choice([-2, -1, 1, 2])) for _ in range(rng.randint(1, 12))]
        u, v = (Fraction(1), Fraction(0)), None
        for x, e in w:   # compose affine maps x -> p x + q on the right
            p, q = mats[x](e)
            u = (u[0] * p, u[0] * q + u[1])
        trivial = u == (Fraction(1), Fraction(0))
        assert trivial == (G.word(w) == G.word([])), ('crosscheck', n, w)


if __name__ == '__main__':
    for n in (2, 3, -2, -3):
        crosscheck(n)
    print('normal form agrees with affine BS(1,n) representation, n in 2,3,-2,-3')
    total = 0
    for m in range(1, 5):
        for n in [k for k in range(-4, 5) if k != 0]:
            cnt = 0
            for P in paths(m, abs(n)):
                check(m, n, P)
                cnt += 1
            total += cnt
            print(f'BS({m},{n}): {cnt} staircase paths OK')
    print('all checks passed;', total, 'generating sets verified')
