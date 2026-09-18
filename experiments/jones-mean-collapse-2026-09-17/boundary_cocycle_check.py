#!/usr/bin/env python3
"""Sanity checks for the Jones mean collapse (claim dyadic-extensive-amenability-if-jones-subgroup-coamenable).

S = dyadics in (0,1) with odd binary digit sum. For h in F, Z_h = {t : P(h t) != P(t)} = h^{-1}S xor S.
Checked on random words in x0, x1 and their inverses:
  (1) Z_h has a constant left germ and a right germ equal to its value at every dyadic x tested;
  (2) the boundary d(Z_h) = {x : [x in Z_h] != left germ} satisfies
        x in d(Z_h)  iff  n(h x) - n(x) + log2 h'(x-) is odd,
      where n(t) is the binary length of t;
  (3) c(g) = d(Z_{g^{-1}}) is finite and is a left cocycle: c(gk) = g c(k) xor c(g);
  (4) c(x0) = {1/2}, c(x1) = {3/4};
  (5) the explicit bump h_x (slope 2 at x-, identity right of x) fixes x and puts x in d(Z_h).
Exit status 0 iff every check passes.
"""
import random
import sys
from fractions import Fraction as Q


def n_len(t):
    d = t.denominator
    k = d.bit_length() - 1
    assert d == 1 << k
    return k


def P(t):
    # parity of the binary digit sum of a dyadic t in (0,1)
    k = n_len(t)
    return bin(t.numerator * ((1 << k) // t.denominator)).count("1") % 2


class PL:
    """Piecewise-linear homeomorphism of [0,1] given by breakpoint list [(a_i, b_i)]."""

    def __init__(self, pts):
        self.pts = pts

    def __call__(self, t):
        p = self.pts
        for (a0, b0), (a1, b1) in zip(p, p[1:]):
            if a0 <= t <= a1:
                return b0 + (b1 - b0) * (t - a0) / (a1 - a0)
        raise ValueError(t)

    def inv(self):
        return PL([(b, a) for a, b in self.pts])

    def breaks(self):
        return [a for a, _ in self.pts]

    def left_slope(self, t):
        p = self.pts
        for (a0, b0), (a1, b1) in zip(p, p[1:]):
            if a0 < t <= a1:
                return (b1 - b0) / (a1 - a0)
        raise ValueError(t)

    def compose(self, other):  # self o other
        xs = set(other.breaks()) | {other.inv()(a) for a in self.breaks()}
        xs = sorted(xs)
        return PL([(x, self(other(x))) for x in xs])


def log2(q):
    num, den = q.numerator, q.denominator
    if num == 1:
        k = den.bit_length() - 1
        assert den == 1 << k
        return -k
    k = num.bit_length() - 1
    assert num == 1 << k and den == 1
    return k


x0 = PL([(Q(0), Q(0)), (Q(1, 2), Q(1, 4)), (Q(3, 4), Q(1, 2)), (Q(1), Q(1))])
x1 = PL([(Q(0), Q(0)), (Q(1, 2), Q(1, 2)), (Q(3, 4), Q(5, 8)), (Q(7, 8), Q(3, 4)), (Q(1), Q(1))])
GENS = [x0, x0.inv(), x1, x1.inv()]


def inZ(h, t):
    return P(h(t)) != P(t)


def boundary_direct(h, maxlen):
    """d(Z_h) restricted to dyadics of length <= maxlen, computed from germs directly."""
    out = set()
    for k in range(1, maxlen + 1):
        for num in range(1, 1 << k, 2):
            x = Q(num, 1 << k)
            K = 40
            left = [inZ(h, x - Q(1, 1 << (K + j))) for j in range(4)]
            right = [inZ(h, x + Q(1, 1 << (K + j))) for j in range(4)]
            assert len(set(left)) == 1, ("left germ not constant", x)
            assert len(set(right)) == 1, ("right germ not constant", x)
            v = inZ(h, x)
            assert right[0] == v, ("right germ differs from value", x)
            formula = (n_len(h(x)) - n_len(x) + log2(h.left_slope(x))) % 2 == 1
            assert (v != left[0]) == formula, ("boundary formula fails", x)
            if v != left[0]:
                out.add(x)
    return out


def c_of(g, maxlen):
    return boundary_direct(g.inv(), maxlen)


def main():
    random.seed(20260917)
    L = 9
    assert c_of(x0, L) == {Q(1, 2)}, c_of(x0, L)
    assert c_of(x1, L) == {Q(3, 4)}, c_of(x1, L)
    for trial in range(25):
        g = PL([(Q(0), Q(0)), (Q(1), Q(1))])
        for _ in range(random.randint(1, 5)):
            g = g.compose(random.choice(GENS))
        k = PL([(Q(0), Q(0)), (Q(1), Q(1))])
        for _ in range(random.randint(1, 5)):
            k = k.compose(random.choice(GENS))
        maxb = max(n_len(a) for a in g.breaks() + k.breaks() + [b for _, b in g.pts + k.pts])
        M = maxb + 8
        cg, ck, cgk = c_of(g, M), c_of(k, M), c_of(g.compose(k), M)
        # finiteness: nothing new appears two lengths further
        assert c_of(g, M + 2) == cg
        assert cgk == {g(t) for t in ck} ^ cg, ("cocycle identity fails", trial)
    for x in [Q(1, 2), Q(3, 8), Q(5, 16), Q(13, 16), Q(1, 64)]:
        d = Q(1, 1 << (n_len(x) + 3))
        h = PL([(Q(0), Q(0)), (x - 4 * d, x - 4 * d), (x - 2 * d, x - 3 * d), (x - d, x - 2 * d),
                (x, x), (Q(1), Q(1))])
        assert h(x) == x and h.left_slope(x) == 2
        assert x in boundary_direct(h, n_len(x) + 6), ("point character trivial", x)
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
