"""Exact checks for pl-chain-germ-group-has-empty-bns-invariant.

y-coordinates: x = Lam(y) = 2^floor(y) (1 + frac(y)).
Checks, in exact rational arithmetic:
  1. Laminv(Lam(y)+1) == e0(y)       (sigma = x+1 becomes the carry map e0)
     Laminv(2 Lam(y))   == y + 1     (delta = 2x becomes T_1)
     Laminv(a(Lam(y)))  == 2 y       (square map a becomes D_2)
  2. 2^(-y-1) <= e0(y) - y <= 2^(1-y) for y >= 0          (kappa(sigma) = 0)
  3. decay order of g_k = D_2^k e0 D_2^-k is k: the ratio
     -log2(g_k(y) - y) * 2^k / y tends to 1                  (item (iv))
  4. u h u^-1 with u = e0, h = g_3 keeps decay order 3      (item (iii))
     and T_(1/2) e0 T_(-1/2) keeps decay order 0.
"""
from fractions import Fraction as Fr
import math
import random


def floor_log2(x):
    n = 0
    while x >= 2:
        x /= 2
        n += 1
    while x < 1:
        x *= 2
        n -= 1
    return n


def Lam(y):
    n = math.floor(y)
    return Fr(2) ** n * (1 + (y - n))


def Laminv(x):
    n = floor_log2(x)
    return n + x / Fr(2) ** n - 1


def a(x):
    # odd dyadic square map on x > 0: a(2x) = 4 a(x)
    m = floor_log2(x)
    u = x / Fr(2) ** m
    base = 2 * u - 1 if u < Fr(3, 2) else 4 * u - 4
    return Fr(4) ** m * base


def e0(y):
    # carry map, y >= 0
    n = math.floor(y)
    if y < n + 1 - Fr(1, 2 ** n):
        return y + Fr(1, 2 ** n)
    return n + 1 + (y - n - 1 + Fr(1, 2 ** n)) / 2


def e0inv(y):
    return Laminv(Lam(y) - 1)


def g(k, y):
    return 2 ** k * e0(y / Fr(2) ** k)


def ratio(res, k, y):
    return -math.log2(float(res)) * 2 ** k / float(y)


def main():
    random.seed(1)
    pts = [Fr(random.randint(0, 40 * 2 ** 12), 2 ** 12) for _ in range(4000)]
    pts += [Fr(n) for n in range(0, 40)] + [n + 1 - Fr(1, 2 ** n) for n in range(0, 30)]
    bad = [0, 0, 0, 0]
    for y in pts:
        if Laminv(Lam(y) + 1) != e0(y):
            bad[0] += 1
        if Laminv(2 * Lam(y)) != y + 1:
            bad[1] += 1
        if Laminv(a(Lam(y))) != 2 * y:
            bad[2] += 1
        r = e0(y) - y
        # 2^(-y-1) <= r <= 2^(1-y), compared through floats of log2 (r is exact)
        lr = math.log2(float(r))
        if not (-float(y) - 1 - 1e-9 <= lr <= 1 - float(y) + 1e-9):
            bad[3] += 1
    print("coordinate identities: e0 mismatches", bad[0], "| T_1 mismatches", bad[1],
          "| D_2 mismatches", bad[2], "| e0 bound failures", bad[3], "| points", len(pts))

    print("decay order of g_k = D_2^k e0 D_2^-k: ratio -log2(res)*2^k/y (tends to 1)")
    for k in range(0, 5):
        row = []
        for y in [Fr(40 * 2 ** k) + Fr(1, 3), Fr(80 * 2 ** k) + Fr(1, 3), Fr(160 * 2 ** k) + Fr(1, 3)]:
            row.append(round(ratio(g(k, y) - y, k, y), 4))
        print("  k =", k, row)

    print("conjugation checks (ratio with the stated order K should tend to 1)")
    for y in [Fr(640) + Fr(1, 3), Fr(1280) + Fr(1, 3), Fr(2560) + Fr(1, 3)]:
        z = e0inv(y)
        w = e0(g(3, z))
        print("  e0 g_3 e0^-1 at y =", float(y), "ratio(K=3) =", round(ratio(w - y, 3, y), 4))
    for y in [Fr(40) + Fr(1, 3), Fr(80) + Fr(1, 3), Fr(160) + Fr(1, 3)]:
        w = e0(y - Fr(1, 2)) + Fr(1, 2)
        print("  T_1/2 e0 T_-1/2 at y =", float(y), "ratio(K=0) =", round(ratio(w - y, 0, y), 4))
    ok = bad == [0, 0, 0, 0]
    print("ALL EXACT CHECKS PASS" if ok else "FAILURES")


if __name__ == "__main__":
    main()
