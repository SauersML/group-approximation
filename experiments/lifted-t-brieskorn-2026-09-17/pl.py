"""Exact PL lifts of Thompson T elements to R.

A lift is a PL homeomorphism of R commuting with x -> x+1, stored by its
breakpoints (x, y) for x in [0, 1], with y(1) = y(0) + 1.  All arithmetic is
exact (Fraction).  Composition and inversion are exact on breakpoints.
"""
from fractions import Fraction as Q
import math


def simplify(pts):
    out = [pts[0]]
    for i in range(1, len(pts) - 1):
        (x0, y0), (x1, y1), (x2, y2) = out[-1], pts[i], pts[i + 1]
        if (y1 - y0) * (x2 - x1) != (y2 - y1) * (x1 - x0):
            out.append(pts[i])
    out.append(pts[-1])
    return out


class Lift:
    def __init__(self, pts):
        self.pts = [(Q(a), Q(b)) for a, b in pts]
        assert self.pts[0][0] == 0 and self.pts[-1][0] == 1
        assert self.pts[-1][1] == self.pts[0][1] + 1
        for i in range(len(self.pts) - 1):
            assert self.pts[i + 1][0] > self.pts[i][0]
            assert self.pts[i + 1][1] > self.pts[i][1]

    def __call__(self, x):
        x = Q(x)
        n = math.floor(x)
        f = x - n
        P = self.pts
        for i in range(len(P) - 1):
            (x0, y0), (x1, y1) = P[i], P[i + 1]
            if x0 <= f <= x1:
                return y0 + (y1 - y0) * (f - x0) / (x1 - x0) + n
        raise ValueError(x)

    def inv(self, y):
        y = Q(y)
        n = math.floor(y - self.pts[0][1])
        g = y - n
        P = self.pts
        for i in range(len(P) - 1):
            (x0, y0), (x1, y1) = P[i], P[i + 1]
            if y0 <= g <= y1:
                return x0 + (x1 - x0) * (g - y0) / (y1 - y0) + n
        raise ValueError(y)

    def __mul__(self, other):
        """(self * other)(x) = self(other(x))."""
        xs = {p[0] for p in other.pts}
        for b, _ in self.pts:
            for k in range(-4, 5):
                x = other.inv(b + k)
                if 0 <= x <= 1:
                    xs.add(x)
        xs = sorted(xs)
        return Lift(simplify([(x, self(other(x))) for x in xs]))

    def inverse(self):
        xs = {Q(0), Q(1)}
        for _, y in self.pts:
            xs.add(y - math.floor(y))
        xs = sorted(xs)
        return Lift(simplify([(x, self.inv(x)) for x in xs]))

    def __pow__(self, n):
        r = ID
        b = self if n >= 0 else self.inverse()
        for _ in range(abs(n)):
            r = b * r
        return r

    def key(self):
        return tuple(self.pts)

    def __eq__(self, o):
        return self.key() == o.key()

    def __hash__(self):
        return hash(self.key())

    def mod1(self):
        """Canonical lift with value at 0 in [0,1): a faithful name for the T element."""
        s = math.floor(self(0))
        return Lift([(x, y - s) for x, y in self.pts])

    def shift(self):
        """If self is a power of z (translation by an integer), return it; else None."""
        if len(self.pts) == 2 and self.pts[0][1] == int(self.pts[0][1]):
            return int(self.pts[0][1])
        return None


ID = Lift([(0, 0), (1, 1)])
Z = Lift([(0, 1), (1, 2)])
