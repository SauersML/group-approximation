#!/usr/bin/env python3
"""Exact-arithmetic referee checks for Steps 2-4 of
research/thompson-f-coarse-reiter-radius-is-one-ramsey-call-away-proof.md.

Elements of Thompson's F are PL homeomorphisms of [0,1] stored as breakpoint lists of
Fractions. Composition convention: (a*b)(t) = a(b(t)) (left action, as in the proof).

Checked on random samples (seeded, deterministic):
  C1  sigma phi_k(y) sigma^-1 == phi_{k+1}(y)                       (Step 2, conjugation)
  C2  phi_k is a homomorphism, phi_k(F) supported in J_k              (Step 2)
  C3  v = z sigma^s u^t is recovered from v by slopes at 0+ and 1/2+  (Step 2/3, exponents)
  C4  restriction lemma N(y_k(v)) <= N(z)                            (Step 3)
  C5  shift identity y_i(sigma^j a_j v) = g_i y_{i-j}(v), 0 <= i < K  (Steps 4-5)
  C6  sigma^j a_j == P sigma^j                                       (Step 4)
  C7  threshold dithering |#{s<8 : x > (s+1/2)/8}/8 - x| <= 1/16     (Step 5)
Prints one line per check and exits nonzero on any failure.
"""
from fractions import Fraction as Fr
import random, sys

H = Fr(1, 2)


class PL:
    __slots__ = ("pts",)

    def __init__(self, pts):
        # pts: list of (x, y), increasing, starting (0,0), ending (1,1); simplify collinear
        out = [pts[0]]
        for p in pts[1:]:
            if p[0] == out[-1][0]:
                continue
            out.append(p)
        simp = [out[0]]
        for i in range(1, len(out) - 1):
            (x0, y0), (x1, y1), (x2, y2) = simp[-1], out[i], out[i + 1]
            if (y1 - y0) * (x2 - x1) == (y2 - y1) * (x1 - x0):
                continue
            simp.append(out[i])
        simp.append(out[-1])
        self.pts = tuple(simp)

    def __call__(self, t):
        p = self.pts
        for i in range(len(p) - 1):
            if p[i][0] <= t <= p[i + 1][0]:
                (a, b), (c, d) = p[i], p[i + 1]
                return b + (d - b) * (t - a) / (c - a)
        raise ValueError(t)

    def inv(self):
        return PL([(y, x) for (x, y) in self.pts])

    def __mul__(self, other):  # self o other
        xs = set(x for x, _ in other.pts)
        oinv = other.inv()
        xs |= set(oinv(x) for x, _ in self.pts)
        xs = sorted(xs)
        return PL([(x, self(other(x))) for x in xs])

    def __eq__(self, other):
        return self.pts == other.pts

    def __hash__(self):
        return hash(self.pts)

    def slope_right(self, t):
        p = self.pts
        for i in range(len(p) - 1):
            if p[i][0] <= t < p[i + 1][0]:
                return (p[i + 1][1] - p[i][1]) / (p[i + 1][0] - p[i][0])
        raise ValueError(t)


E = PL([(Fr(0), Fr(0)), (Fr(1), Fr(1))])
X0 = PL([(Fr(0), Fr(0)), (H, Fr(1, 4)), (Fr(3, 4), H), (Fr(1), Fr(1))])


def conj_into(y, a, b):
    """The element acting on [a,b] as the affine rescaling of y, identity elsewhere."""
    L = b - a
    pts = [(Fr(0), Fr(0))]
    if a > 0:
        pts.append((a, a))
    pts += [(a + L * x, a + L * yy) for (x, yy) in y.pts]
    if b < 1:
        pts.append((Fr(1), Fr(1)))
    return PL(pts)


X1 = conj_into(X0, H, Fr(1))
SIGMA = conj_into(X0, Fr(0), H)
U = X1


def I(k):
    if k >= 0:
        return (Fr(1, 2 ** (k + 2)), Fr(1, 2 ** (k + 1)))
    k = -k
    return (1 - Fr(1, 2 ** k), 1 - Fr(1, 2 ** (k + 1)))


def J(k):
    a, b = I(k)
    return (a / 2, b / 2)


def phi(k, y):
    a, b = J(k)
    return conj_into(y, a, b)


def restrict(z, a, b):
    """alpha^-1 z|_[a,b] alpha, assuming z([a,b]) = [a,b]."""
    assert z(a) == a and z(b) == b
    L = b - a
    xs = sorted(set([a, b] + [x for x, _ in z.pts if a < x < b]))
    return PL([((x - a) / L, (z(x) - a) / L) for x in xs])


def is_dyadic(a, b):
    L = b - a
    if L <= 0 or L.numerator != 1 or (L.denominator & (L.denominator - 1)):
        return False
    return (a / L).denominator == 1


def carets(f):
    """N(f): leaves - 1 of the reduced tree pair (maximal good standard dyadic intervals)."""
    xs = [x for x, _ in f.pts]

    def affine_on(a, b):
        return not any(a < x < b for x in xs)

    def rec(a, b):
        if affine_on(a, b) and is_dyadic(f(a), f(b)):
            return 1
        m = (a + b) / 2
        return rec(a, m) + rec(m, b)

    return rec(Fr(0), Fr(1)) - 1


def power(g, n):
    r = E
    base = g if n >= 0 else g.inv()
    for _ in range(abs(n)):
        r = base * r
    return r


def rand_word(rng, length):
    gens = [X0, X0.inv(), X1, X1.inv()]
    w = E
    for _ in range(length):
        w = rng.choice(gens) * w
    return w


def log2(q):
    n = 0
    while q > 1:
        q /= 2
        n += 1
    while q < 1:
        q *= 2
        n -= 1
    assert q == 1
    return n


def decompose(v, krange):
    s = -log2(v.slope_right(Fr(0)))
    t = -log2(v.slope_right(H))
    z = v * power(U, -t) * power(SIGMA, -s)
    ys = {}
    for k in krange:
        a, b = J(k)
        ys[k] = restrict(z, a, b)
    return z, s, t, ys


def main():
    rng = random.Random(20260917)
    ok = True

    def report(name, cond):
        nonlocal ok
        ok &= cond
        print(("PASS " if cond else "FAIL ") + name)

    report("C0 sanity: N(e)=0, N(x0)=2, N(x1)=3, slopes of sigma at 0+ is 1/2",
           (carets(E), carets(X0), carets(X1), SIGMA.slope_right(Fr(0))) == (0, 2, 3, H))
    ks = range(-3, 4)
    samples = [rand_word(rng, rng.randint(1, 6)) for _ in range(12)]
    # C1
    report("C1 sigma phi_k(y) sigma^-1 = phi_{k+1}(y)",
           all(SIGMA * phi(k, y) * SIGMA.inv() == phi(k + 1, y) for y in samples for k in ks))
    # C2
    c2 = True
    for y1, y2 in zip(samples, samples[1:]):
        for k in ks:
            c2 &= phi(k, y1 * y2) == phi(k, y1) * phi(k, y2)
            a, b = J(k)
            c2 &= all(x == yy for x, yy in phi(k, y1).pts if x <= a or x >= b)
            c2 &= restrict(phi(k, y1), a, b) == y1
    report("C2 phi_k homomorphism, recovered by restriction", c2)
    # random v in V: z sigma^s u^t with z = prod phi_k(y_k)
    c3 = c4 = True
    for trial in range(15):
        yk = {k: rand_word(rng, rng.randint(0, 5)) for k in ks}
        z = E
        for k in ks:
            z = phi(k, yk[k]) * z
        s, t = rng.randint(-3, 3), rng.randint(-3, 3)
        v = z * power(SIGMA, s) * power(U, t)
        z2, s2, t2, ys = decompose(v, ks)
        c3 &= (s2, t2) == (s, t) and z2 == z and all(ys[k] == yk[k] for k in ks)
        c4 &= all(carets(ys[k]) <= carets(z) for k in ks)
    report("C3 slopes at 0+ and 1/2+ give s and t; coordinates recovered", c3)
    report("C4 restriction lemma N(y_k) <= N(z)", c4)
    # C5, C6 with K = 3
    K = 3
    g = [rand_word(rng, rng.randint(1, 4)) for _ in range(K)]
    P = E
    for i in range(K):
        P = phi(i, g[i]) * P
    c5 = c6 = True
    for j in range(0, 4):
        a_j = E
        for i in range(K):
            a_j = phi(i - j, g[i]) * a_j
        c6 &= power(SIGMA, j) * a_j == P * power(SIGMA, j)
        for trial in range(3):
            yk = {k: rand_word(rng, rng.randint(0, 3)) for k in range(-6, 4)}
            z = E
            for k in yk:
                z = phi(k, yk[k]) * z
            v = z * power(SIGMA, rng.randint(-2, 2)) * power(U, rng.randint(-2, 2))
            _, _, _, ya = decompose(power(SIGMA, j) * a_j * v, range(0, K))
            _, _, _, yv = decompose(v, range(-6, 4))
            _, _, _, ys = decompose(power(SIGMA, j) * v, range(0, K))
            c5 &= all(ya[i] == g[i] * yv[i - j] for i in range(K))
            c5 &= all(ys[i] == yv[i - j] for i in range(K))
    report("C5 shift identity y_i(sigma^j a_j v) = g_i y_{i-j}(v), y_i(sigma^j v) = y_{i-j}(v)", c5)
    report("C6 sigma^j a_j = P sigma^j", c6)
    c7 = all(abs(Fr(sum(1 for s in range(8) if x > Fr(2 * s + 1, 16)), 8) - x) <= Fr(1, 16)
             for x in [Fr(n, 997) for n in range(998)])
    report("C7 threshold dithering error <= 1/16", c7)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
