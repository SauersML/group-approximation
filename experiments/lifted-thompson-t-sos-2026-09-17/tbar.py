"""Exact arithmetic for the lift T-bar of Thompson's group T to the real line.

An element g of T-bar is a PL homeomorphism of R with dyadic breakpoints and
slopes in 2^Z commuting with z(x) = x + 1.  It is stored by its restriction to
[0, 1]: a tuple of breakpoints 0 = a_0 < ... < a_m = 1 and the tuple of values
g(a_i), with g(1) = g(0) + 1.  Only genuine breakpoints are kept (slope changes),
plus the endpoints 0 and 1, so the pair (breaks, values) is a canonical key.
"""
from fractions import Fraction as Fr
import math


def floor_fr(x):
    return x.numerator // x.denominator


class TBar:
    __slots__ = ("a", "b", "_h")

    def __init__(self, a, b, canon=True):
        a = tuple(Fr(t) for t in a)
        b = tuple(Fr(t) for t in b)
        assert a[0] == 0 and a[-1] == 1 and b[-1] == b[0] + 1
        if canon:
            a, b = _reduce(a, b)
        self.a, self.b = a, b
        self._h = hash((a, b))

    def __hash__(self):
        return self._h

    def __eq__(self, o):
        return self.a == o.a and self.b == o.b

    # evaluation on R
    def __call__(self, x):
        x = Fr(x)
        n = floor_fr(x)
        t = x - n
        a, b = self.a, self.b
        # binary search for interval
        lo, hi = 0, len(a) - 1
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if a[mid] <= t:
                lo = mid
            else:
                hi = mid
        s = (b[lo + 1] - b[lo]) / (a[lo + 1] - a[lo])
        return b[lo] + s * (t - a[lo]) + n

    def inv(self):
        # g^{-1} maps [g(0), g(0)+1] -> [0,1]; re-base to [0,1]
        a, b = self.a, self.b
        pts = set()
        g0 = b[0]
        # breakpoints of g^{-1} in [0,1): values b_i reduced mod 1
        for v in b:
            pts.add(v - floor_fr(v))
        pts.add(Fr(0))
        pts = sorted(pts)
        ginv = lambda y: _inv_eval(a, b, y)
        aa = pts + [Fr(1)]
        bb = [ginv(t) for t in aa]
        return TBar(aa, bb)

    def __mul__(self, o):
        # (self * o)(x) = self(o(x))
        pts = set(o.a)
        lo_, hi_ = o.b[0], o.b[-1]
        # breakpoints of self translated into [lo_, hi_]
        n0 = floor_fr(lo_) - 1
        n1 = floor_fr(hi_) + 1
        for n in range(n0, n1 + 1):
            for t in self.a:
                y = t + n
                if lo_ <= y <= hi_:
                    pts.add(_inv_eval(o.a, o.b, y))
        aa = sorted(p for p in pts if 0 <= p <= 1)
        bb = [self(o(t)) for t in aa]
        return TBar(aa, bb)

    def __pow__(self, k):
        r = identity()
        base = self if k >= 0 else self.inv()
        for _ in range(abs(k)):
            r = r * base
        return r

    def __repr__(self):
        return "TBar(%s -> %s)" % ([str(x) for x in self.a], [str(x) for x in self.b])


def _inv_eval(a, b, y):
    """Evaluate g^{-1}(y) for arbitrary real y, g given on [0,1] by (a,b)."""
    y = Fr(y)
    # shift y into [b0, b0+1)
    n = floor_fr(y - b[0])
    y0 = y - n
    lo, hi = 0, len(b) - 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if b[mid] <= y0:
            lo = mid
        else:
            hi = mid
    s = (a[lo + 1] - a[lo]) / (b[lo + 1] - b[lo])
    return a[lo] + s * (y0 - b[lo]) + n


def _reduce(a, b):
    aa, bb = [a[0]], [b[0]]
    for i in range(1, len(a) - 1):
        s1 = (b[i] - bb[-1]) / (a[i] - aa[-1])
        s2 = (b[i + 1] - b[i]) / (a[i + 1] - a[i])
        if s1 != s2:
            aa.append(a[i])
            bb.append(b[i])
    aa.append(a[-1])
    bb.append(b[-1])
    # slope across the point 1 ~ 0 is not a breakpoint issue: keep 0 and 1 always
    return tuple(aa), tuple(bb)


def identity():
    return TBar([0, 1], [0, 1])


def z():
    return TBar([0, 1], [1, 2])


H = Fr(1, 2)
Q = Fr(1, 4)
E = Fr(1, 8)

X0 = TBar([0, H, 3 * Q, 1], [0, Q, H, 1])
X1 = TBar([0, H, 3 * Q, 7 * E, 1], [0, H, 5 * E, 3 * Q, 1])
# lift of the order-3 element c of T with c(0) = 3/4
C = TBar([0, H, 3 * Q, 1], [3 * Q, 1, 3 * H, 7 * Q])


def check_slopes(g):
    for i in range(len(g.a) - 1):
        s = (g.b[i + 1] - g.b[i]) / (g.a[i + 1] - g.a[i])
        l = math.log2(s)
        assert l == int(l), g
        assert s.denominator in (1,) or s.numerator == 1
    return True


if __name__ == "__main__":
    for g in (X0, X1, C):
        check_slopes(g)
        assert g * g.inv() == identity(), g
        assert g.inv() * g == identity(), g
    print("c^3 =", C ** 3)
    print("z   =", z())
    print("c^3 == z:", C ** 3 == z(), " c^3 == z^2:", C ** 3 == z() ** 2)
    # z central
    for g in (X0, X1, C):
        assert g * z() == z() * g
    print("ok")
