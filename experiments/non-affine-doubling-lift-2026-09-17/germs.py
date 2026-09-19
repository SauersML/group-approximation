"""Pointwise exact evaluation of chain-configuration germs at +infinity.

sigma(x) = x + 1.  delta is the lift of a degree-2 circle map, given by one
period d : [0,1) -> [d(0), d(0)+2) (increasing, PL); delta(n + r) = 2n + d(r).
s is built from a PL homeomorphism s0 : [X, delta(X)) -> [Y, delta^2(Y)) and
extended by s(delta^n x) = delta^(2n) s0(x), so s delta s^-1 = delta^2 exactly.
All arithmetic is exact (Fractions).
"""
from fractions import Fraction as Fr
from math import floor


class PL1:
    """Increasing PL map on a half-open interval, given by breakpoints and values."""

    def __init__(self, xs, ys):
        self.xs = [Fr(v) for v in xs]
        self.ys = [Fr(v) for v in ys]

    def __call__(self, x):
        xs, ys = self.xs, self.ys
        assert xs[0] <= x < xs[-1], (x, xs[0], xs[-1])
        for i in range(len(xs) - 1):
            if x < xs[i + 1]:
                return ys[i] + (ys[i + 1] - ys[i]) * (x - xs[i]) / (xs[i + 1] - xs[i])
        raise AssertionError

    def inv(self):
        return PL1(self.ys, self.xs)


class Chain:
    def __init__(self, d_xs, d_ys, X, s0_xs, s0_ys):
        self.d = PL1(d_xs, d_ys)          # on [0,1)
        self.dinv = self.d.inv()          # on [d(0), d(0)+2)
        self.d0 = self.d.ys[0]
        self.X = Fr(X)
        self.s0 = PL1(s0_xs, s0_ys)
        self.s0inv = self.s0.inv()
        assert self.s0.xs[0] == self.X and self.s0.xs[-1] == self.delta(self.X)
        Y = self.s0.ys[0]
        assert self.s0.ys[-1] == self.delta(self.delta(Y))
        self.Y = Y

    def delta(self, x):
        n = floor(x)
        return 2 * n + self.d(x - n)

    def delta_inv(self, y):
        n = floor((y - self.d0) / 2)
        return n + self.dinv(y - 2 * n)

    def s(self, x):
        n = 0
        while x >= self.delta(self.X):
            x = self.delta_inv(x)
            n += 1
        assert x >= self.X
        y = self.s0(x)
        for _ in range(2 * n):
            y = self.delta(y)
        return y

    def s_inv(self, y):
        n = 0
        top = self.delta(self.delta(self.Y))
        while y >= top:
            y = self.delta_inv(self.delta_inv(y))
            n += 1
        assert y >= self.Y
        x = self.s0inv(y)
        for _ in range(n):
            x = self.delta(x)
        return x

    # group elements as functions -------------------------------------------
    def tau(self, x):
        return self.s_inv(self.s(x) + 1)

    def tau_inv(self, x):
        return self.s_inv(self.s(x) - 1)

    def c1(self, x):          # tau sigma tau^-1 sigma^-1
        return self.tau(self.tau_inv(x - 1) + 1)

    def c1_inv(self, x):      # sigma tau sigma^-1 tau^-1
        return self.tau(self.tau_inv(x) - 1) + 1

    def ck(self, k, x):       # sigma^k c1 sigma^-k
        return self.c1(x - k) + k

    def ck_inv(self, k, x):
        return self.c1_inv(x - k) + k

    def w(self, k, x):        # [c1, ck] = c1 ck c1^-1 ck^-1
        return self.c1(self.ck(k, self.c1_inv(self.ck_inv(k, x))))


def affine_control():
    """delta = 2x, s0 = the odd dyadic square map rescaled to [4,8) -> [16,64)."""
    return Chain([0, 1], [0, 2], 4, [4, 6, 8], [16, 32, 64])


def nonaffine():
    """d: slope 1 on [0,1/2), 2 on [1/2,3/4), 4 on [3/4,1); d(0)=1/2."""
    d_xs = [0, Fr(1, 2), Fr(3, 4), 1]
    d_ys = [Fr(1, 2), 1, Fr(3, 2), Fr(5, 2)]
    # delta(4) = 17/2, delta(16) = 65/2, delta(65/2) = 65.
    s0_xs = [4, 8, Fr(33, 4), Fr(17, 2)]
    s0_ys = [16, 48, 49, 65]
    return Chain(d_xs, d_ys, 4, s0_xs, s0_ys)
