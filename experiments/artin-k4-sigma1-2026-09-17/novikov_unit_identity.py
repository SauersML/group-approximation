#!/usr/bin/env python3
"""Mechanical check of the Novikov unit identity for A_K,
K = K4, labels u1u2:2, v1v2:2, u1v1:4, u2v1:4, u2v2:4, u1v2:6, chi=(1,1,-1,-1).
This is Kochloukova's Example 7.1 (arXiv:2009.14269, Section 7) under
s=u1, v=u2, u=v2, w=v1 (m_vs=m_uw=1, m_uv=m_vw=m_ws=2, m_su=3).

Checks, in the integral group ring of the FREE group F(a,b,c,e)
(a=u1, b=u2, c=v1, e=v2):
 (1) Fox derivative of r=(xy)^k (yx)^-k wrt x equals
     S_k(xy) - r * S_k(yx) y   and   S_k(yx) y == y S_k(xy)   (free group),
     so in G: d r/dx = (1-y) S_k(xy).
 (2) the identity
     [S3(ae) - ae S2(ac)](a-1) + a e a b^-1 [S2(bc) - S2(be)](b-1)
        == (a-1) + a e a (e-c)(a-b)
     holds in Z F(a,b,c,e).
 (3) every word of a e a (e-c)(a-b) has chi >= 1, so
     (a-1)^-1 a e a (e-c)(a-b) = -sum_{n>=0} a^n (...) has chi >= 1 terms only,
     finitely many per level: 1 + delta is a unit of the Novikov ring.
"""
from collections import defaultdict

CHI = {'a': 1, 'b': 1, 'c': -1, 'e': -1}


def red(w):
    out = []
    for g in w:
        if out and out[-1][0] == g[0] and out[-1][1] == -g[1]:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


class R:
    def __init__(self, d=None):
        self.d = {k: v for k, v in (d or {}).items() if v}

    @staticmethod
    def w(s):  # "a b B" uppercase = inverse
        return R({red(tuple((t.lower(), 1 if t.islower() else -1) for t in s.split())): 1})

    def __add__(self, o):
        d = defaultdict(int, self.d)
        for k, v in o.d.items():
            d[k] += v
        return R(d)

    def __neg__(self):
        return R({k: -v for k, v in self.d.items()})

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        d = defaultdict(int)
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                d[red(k1 + k2)] += v1 * v2
        return R(d)

    def __eq__(self, o):
        return (self - o).d == {}


ONE = R({(): 1})


def S(k, x):
    tot, p = R(), ONE
    for _ in range(k):
        tot, p = tot + p, p * x
    return tot


def fox(word, g):
    """word: list of (gen, +-1); Fox derivative wrt gen g in Z F."""
    tot, pref = R(), ONE
    for (h, e) in word:
        if e == 1:
            if h == g:
                tot = tot + pref
            pref = pref * R({((h, 1),): 1})
        else:
            pref = pref * R({((h, -1),): 1})
            if h == g:
                tot = tot - pref
    return tot


def braid(x, y, m):
    X = [(x, 1) if i % 2 == 0 else (y, 1) for i in range(m)]
    Y = [(y, 1) if i % 2 == 0 else (x, 1) for i in range(m)]
    return X + [(g, -e) for (g, e) in reversed(Y)]


def gen(x):
    return R({((x, 1),): 1})


ok = True
for (x, y, m) in [('a', 'c', 4), ('b', 'c', 4), ('b', 'e', 4), ('a', 'e', 6)]:
    k = m // 2
    r = braid(x, y, m)
    rw = R({red(tuple(r)): 1})
    X, Y = gen(x), gen(y)
    c1 = fox(r, x) == S(k, X * Y) - rw * S(k, Y * X) * Y
    c2 = S(k, Y * X) * Y == Y * S(k, X * Y)
    print("edge", x + y, "label", m, "fox formula", c1, "shift", c2)
    ok &= c1 and c2

a, b, c, e = gen('a'), gen('b'), gen('c'), gen('e')
binv = R.w("B")
lhs = (S(3, a * e) - a * e * S(2, a * c)) * (a - ONE) \
    + a * e * a * binv * (S(2, b * c) - S(2, b * e)) * (b - ONE)
core = a * e * a * (e - c) * (a - b)
rhs = (a - ONE) + core
c3 = lhs == rhs
print("unit identity holds in Z F(a,b,c,e):", c3)
ok &= c3
levels = sorted(sum(CHI[g] * s for (g, s) in wd) for wd in core.d)
print("chi of words in a e a (e-c)(a-b):", levels)
ok &= min(levels) >= 1
print("ALL OK" if ok else "FAIL")
