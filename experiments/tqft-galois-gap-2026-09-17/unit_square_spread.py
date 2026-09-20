"""Unit-square spread lemma check.

For n >= 2 and gcd(k, n) = 1 let
    g(n, k) = max over units j mod n of || k j^2 / n ||_{R/Z}.
The route of mod-s2-tqft-twist-spectra-obey-the-cube-root-gap proves
g(n, k) >= 1/64 for all n, k.  This script computes
    c(N) = min over 2 <= n <= N, gcd(k, n) = 1 of g(n, k)
exactly (rational arithmetic) and reports the minimizers.
Usage: python3 unit_square_spread.py [N]
"""
import sys
from fractions import Fraction
from math import gcd


def dist(num, n):
    r = num % n
    return Fraction(min(r, n - r), n)


def spread(n):
    units = [j for j in range(1, n + 1) if gcd(j, n) == 1]
    squares = sorted({(j * j) % n for j in units})
    return [(max(dist(k * q, n) for q in squares), k) for k in units]


def main(N):
    best, arg = None, []
    worst = None
    for n in range(2, N + 1):
        for g, k in spread(n):
            if best is None or g < best:
                best, arg = g, [(n, k)]
            elif g == best and len(arg) < 12:
                arg.append((n, k))
            if 24 % n != 0 and (worst is None or g < worst[0]):
                worst = (g, n, k)
    print("N =", N, " c(N) =", best, "=", float(best))
    print("minimizers (n, k):", arg)
    print("n not dividing 24: min g =", worst[0], "=", float(worst[0]),
          "at (n, k) =", worst[1:])


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 600)
