#!/usr/bin/env python3
"""Return probabilities of mu = uniform{S, T, T^-1} on PSL2(Z), for the calibrator lower bound
Lambda >= -log((1+rho)/2) of f-dyadic-rare-confinement-rate-at-most-cogrowth-exponent.

Exact rational DP over group elements (matrices mod +-1) up to 2n steps; prints p_{2n}(e,e), the root
p_{2n}^{1/2n} (a lower bound for rho that increases to rho) and the ratio sqrt(p_{2n}/p_{2n-2}).
Usage: python3 psl_return.py [--steps 32]   (runtime: a few minutes and about 2 GB for 32; psl_return.log has t <= 32)
"""
import argparse
import math
from fractions import Fraction


def canon(m):
    a, b, c, d = m
    if a < 0 or (a == 0 and b < 0):
        return (-a, -b, -c, -d)
    return m


def mul(m, n):
    a, b, c, d = m
    e, f, g, h = n
    return canon((a * e + b * g, a * f + b * h, c * e + d * g, c * f + d * h))


GENS = [(0, -1, 1, 0), (1, 1, 0, 1), (1, -1, 0, 1)]
E = (1, 0, 0, 1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--steps", type=int, default=32)
    a = ap.parse_args()
    dist = {E: 1}
    pprev = None
    for t in range(1, a.steps + 1):
        new = {}
        for g, c in dist.items():
            for s in GENS:
                h = mul(g, s)
                new[h] = new.get(h, 0) + c
        dist = new
        if t % 2 == 0:
            p = Fraction(dist.get(E, 0), 3 ** t)
            ratio = math.sqrt(float(p / pprev)) if pprev else float("nan")
            print(t, len(dist), float(p), round(float(p) ** (1 / t), 5), round(ratio, 5), flush=True)
            pprev = p


if __name__ == "__main__":
    main()
