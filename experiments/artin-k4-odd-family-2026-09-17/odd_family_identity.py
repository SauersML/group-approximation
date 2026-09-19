#!/usr/bin/env python3
"""Checks for artin-k4-odd-family-dead-characters-lie-in-sigma1.

Graph K_q: vertices a=u1, b=u2 (chi=+1) and c=v1, e=v2 (chi=-1); labels
l(ab)=l(ce)=2, l(ac)=l(bc)=l(be)=4, l(ae)=2q with q odd.

Checks, all in the integral group ring Z F(a,b,c,e) of the FREE group:
 (1) Fox derivatives of r=(xy)^k (yx)^{-k}:
     d r/dx = S_k(xy) - r * y S_k(xy),  d r/dy = S_k(xy) x - r * S_k(yx),
     and the fundamental formula sum_x (dr/dx)(x-1) = r-1.  Reading r=1 in G
     gives d r/dx = (1-y) S_k(xy), d r/dy = (x-1) S_k(yx).
 (2) For q = 2m+1 (3 <= q <= 41), with x = ae, T = sum_{j<m} x^{2j}:
       x^{2m} = S_q(x) - T S_2(ac) + T a b^-1 S_2(bc) - T a b^-1 S_2(be).
 (3) Every coefficient word (x^{-2m}, x^{-2m} T, x^{-2m} T a b^-1) has chi = 0,
     so 1 = sum lambda_ij S(u_i v_j) with lambda_ij in Z[ker chi].
 (4) The swap sigma: a<->e, b<->c preserves the labelled graph and chi o sigma = -chi.
"""
from collections import defaultdict

GENS = "abce"
CHI = {"a": 1, "b": 1, "c": -1, "e": -1}


def red(w):
    out = []
    for g in w:
        if out and out[-1][0] == g[0] and out[-1][1] == -g[1]:
            out.pop()
        else:
            out.append(g)
    return tuple(out)


def W(s):
    """word from string; capital letter = inverse."""
    return red(tuple((ch.lower(), -1 if ch.isupper() else 1) for ch in s))


def inv(w):
    return tuple((g, -e) for g, e in reversed(w))


class R:
    def __init__(self, d=None):
        self.d = defaultdict(int)
        if d:
            for k, v in d.items():
                if v:
                    self.d[k] += v

    @staticmethod
    def g(w):
        return R({w if isinstance(w, tuple) else W(w): 1})

    def __add__(self, o):
        r = R(self.d)
        for k, v in o.d.items():
            r.d[k] += v
        return r.clean()

    def __neg__(self):
        return R({k: -v for k, v in self.d.items()})

    def __sub__(self, o):
        return self + (-o)

    def __mul__(self, o):
        r = R()
        for k1, v1 in self.d.items():
            for k2, v2 in o.d.items():
                r.d[red(k1 + k2)] += v1 * v2
        return r.clean()

    def clean(self):
        self.d = defaultdict(int, {k: v for k, v in self.d.items() if v})
        return self

    def __eq__(self, o):
        return dict((self - o).d) == {}


ONE = R.g(())


def S(k, z):
    tot, p = R(), ONE
    for _ in range(k):
        tot, p = tot + p, p * z
    return tot


def power(z, n):
    p = ONE
    for _ in range(n):
        p = p * z
    return p


def fox(w, x):
    """Fox derivative d w / d x in Z F."""
    tot, pre = R(), ()
    for g, e in w:
        if g == x:
            if e == 1:
                tot = tot + R.g(pre)
            else:
                tot = tot - R.g(red(pre + ((g, -1),)))
        pre = red(pre + ((g, e),))
    return tot


def chi(w):
    return sum(CHI[g] * e for g, e in w)


def check_fox():
    for x, y in [("a", "c"), ("b", "c"), ("b", "e"), ("a", "e")]:
        for k in (2, 3, 5, 7):
            r = red(W((x + y) * k) + inv(W((y + x) * k)))
            X, Y, Rr = R.g(x), R.g(y), R.g(r)
            assert fox(r, x) == S(k, X * Y) - Rr * Y * S(k, X * Y)
            assert fox(r, y) == S(k, X * Y) * X - Rr * S(k, Y * X)
            lhs = R()
            for g in GENS:
                lhs = lhs + fox(r, g) * (R.g(g) - ONE)
            assert lhs == Rr - ONE
    print("(1) Fox derivatives and fundamental formula: ok")


def check_identity(qmax=41):
    a, b, c, e = (R.g(ch) for ch in "abce")
    Binv = R.g("B")
    x = a * e
    for q in range(3, qmax + 1, 2):
        m = (q - 1) // 2
        T = R()
        for j in range(m):
            T = T + power(x, 2 * j)
        rhs = (S(q, x) - T * S(2, a * c) + T * a * Binv * S(2, b * c)
               - T * a * Binv * S(2, b * e))
        assert rhs == power(x, 2 * m), q
        coeffs = [power(R.g(inv(W("ae"))), 2 * m) * T,
                  power(R.g(inv(W("ae"))), 2 * m) * T * a * Binv,
                  power(R.g(inv(W("ae"))), 2 * m)]
        for cf in coeffs:
            assert all(chi(w) == 0 for w in cf.d), q
    print(f"(2),(3) unit identity and chi=0 coefficients for odd q in [3,{qmax}]: ok")


def check_symmetry():
    sig = {"a": "e", "e": "a", "b": "c", "c": "b"}
    for q in (3, 5, 7):
        lab = {frozenset("ab"): 2, frozenset("ce"): 2, frozenset("ac"): 4,
               frozenset("bc"): 4, frozenset("be"): 4, frozenset("ae"): 2 * q}
        for ed, l in lab.items():
            assert lab[frozenset(sig[v] for v in ed)] == l
        assert all(CHI[sig[v]] == -CHI[v] for v in GENS)
    print("(4) sigma preserves labels, chi o sigma = -chi: ok")


if __name__ == "__main__":
    check_fox()
    check_identity()
    check_symmetry()
