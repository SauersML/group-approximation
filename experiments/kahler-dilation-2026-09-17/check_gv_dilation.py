"""Exact checks for thompson-t-cup-classes-split-along-dilation-eigenlines.

An element of Thompson's T is stored by a lift on [0, 1]: breakpoints xs (0 = x_0 < ... < x_n = 1)
and values ys (increasing, ys[-1] = ys[0] + 1). All arithmetic is exact (Fractions); one-sided
slopes are read off the pieces, never by numerical differentiation.

Checks:
  1. Omega is a 2-cocycle (random triples).
  2. <gv, sigma_t> = 2 for the explicit commuting pair (g_0, h_0).
  3. <gv, J_* sigma_t> = 4, using the half-rotation-equivariant lifts (g_1, h_1).
  4. i^* Omega = 2 p^* Omega on random pairs of C = C_T(x -> x + 1/2).
"""
from fractions import Fraction as Fr
import random


def ilog2(q):
    q = Fr(q)
    n = 0
    while q > 1:
        q /= 2
        n += 1
    while q < 1:
        q *= 2
        n -= 1
    assert q == 1, "slope is not a power of 2"
    return n


class PL:
    def __init__(self, xs, ys):
        assert xs[0] == 0 and xs[-1] == 1 and ys[-1] == ys[0] + 1
        assert all(xs[i] < xs[i + 1] for i in range(len(xs) - 1))
        assert all(ys[i] < ys[i + 1] for i in range(len(ys) - 1))
        self.xs, self.ys = list(xs), list(ys)

    def piece(self, r, side):
        """index of the piece containing r in [0,1), approaching from side (-1 left, +1 right)."""
        for i in range(len(self.xs) - 1):
            a, b = self.xs[i], self.xs[i + 1]
            if side > 0 and a <= r < b:
                return i
            if side < 0 and a < r <= b:
                return i
        raise ValueError

    def lift(self, x):
        k = x.numerator // x.denominator
        r = x - k
        i = self.piece(r, +1)
        a, b = self.xs[i], self.xs[i + 1]
        return k + self.ys[i] + (self.ys[i + 1] - self.ys[i]) * (r - a) / (b - a)

    def __call__(self, x):
        return self.lift(x) % 1

    def slope(self, i):
        return (self.ys[i + 1] - self.ys[i]) / (self.xs[i + 1] - self.xs[i])

    def v(self, y):
        """(log2 f'_-(y), log2 f'_+(y)) for y in S^1."""
        y = Fr(y) % 1
        right = self.slope(self.piece(y, +1))
        left = self.slope(self.piece(y if y != 0 else Fr(1), -1))
        return (ilog2(left), ilog2(right))

    def bps(self):
        return {x % 1 for x in self.xs}

    def preimage(self, b):
        """the unique y in [0,1) with f(y) = b mod 1."""
        for i in range(len(self.xs) - 1):
            lo, hi = self.ys[i], self.ys[i + 1]
            for k in range(-3, 4):
                bb = b + k
                if lo <= bb < hi:
                    a, c = self.xs[i], self.xs[i + 1]
                    return (a + (bb - lo) * (c - a) / (hi - lo)) % 1
        raise ValueError


def compose(f, g):
    """f∘g."""
    cand = set(g.bps()) | {g.preimage(b) for b in f.bps()} | {Fr(0)}
    xs = sorted(cand) + [Fr(1)]
    ys = [f.lift(g.lift(x)) for x in xs]
    sh = ys[0] - (ys[0] % 1)
    return PL(xs, [y - sh for y in ys])


def Omega(f, g):
    pts = set(g.bps()) | {g.preimage(b) for b in f.bps()}
    tot = 0
    for y in pts:
        a, b = g.v(y), f.v(g(y))
        tot += a[0] * b[1] - a[1] * b[0]
    return tot


def rand_T(rng):
    def partition(n):
        ivs = [(Fr(0), Fr(1))]
        while len(ivs) < n:
            i = rng.randrange(len(ivs))
            a, b = ivs.pop(i)
            m = (a + b) / 2
            ivs[i:i] = [(a, m), (m, b)]
        return sorted(ivs)
    n = rng.randint(2, 6)
    P, Q = partition(n), partition(n)
    s = rng.randrange(n)
    xs = [a for a, _ in P] + [Fr(1)]
    ys = [Q[(i + s) % n][0] + (1 if i + s >= n else 0) for i in range(n)]
    return PL(xs, ys + [ys[0] + 1])


def g0():
    return PL([Fr(0), Fr(1, 4), Fr(5, 16), Fr(3, 8), Fr(1, 2), Fr(1)],
              [Fr(0), Fr(1, 4), Fr(3, 8), Fr(7, 16), Fr(1, 2), Fr(1)])


def h0():
    return PL([Fr(0), Fr(1, 2), Fr(9, 16), Fr(5, 8), Fr(3, 4), Fr(1)],
              [Fr(0), Fr(1, 2), Fr(5, 8), Fr(11, 16), Fr(3, 4), Fr(1)])


def half_lift(f):
    """g in C_T(r) with p(g) = f: lift x -> F(2x)/2."""
    xs = sorted({x / 2 for x in f.xs} | {Fr(1, 2) + x / 2 for x in f.xs})
    return PL(xs, [f.lift(2 * x) / 2 for x in xs])


def same(f, g):
    grid = sorted(f.bps() | g.bps() | {Fr(k, 256) for k in range(256)})
    return all(f(x) == g(x) for x in grid)


def main():
    rng = random.Random(20260920)
    for _ in range(60):
        f, g, h = rand_T(rng), rand_T(rng), rand_T(rng)
        d = Omega(g, h) - Omega(compose(f, g), h) + Omega(f, compose(g, h)) - Omega(f, g)
        assert d == 0, d
    print("cocycle identity: ok on 60 random triples")

    G, H = g0(), h0()
    assert same(compose(G, H), compose(H, G))
    t = Omega(G, H) - Omega(H, G)
    print("<gv, sigma_t> =", t)
    assert t == 2

    G1, H1 = half_lift(G), half_lift(H)
    assert same(compose(G1, H1), compose(H1, G1))
    t1 = Omega(G1, H1) - Omega(H1, G1)
    print("<gv, J_* sigma_t> =", t1)
    assert t1 == 4

    for _ in range(60):
        a, b = rand_T(rng), rand_T(rng)
        A, B = half_lift(a), half_lift(b)
        assert Omega(A, B) == 2 * Omega(a, b), (Omega(A, B), Omega(a, b))
    print("i^* Omega = 2 p^* Omega: ok on 60 random pairs in C")


if __name__ == "__main__":
    main()
