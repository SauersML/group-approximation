#!/usr/bin/env python3
"""Two-dimensional representations of partial Burnside groups Pi_R(2,5).

A pair (a,b) in SL_2(C) whose image in PSL_2(C) satisfies h^5 = 1 for every
word h of length <= R.  In SL_2(C), g has order dividing 5 in PSL_2 iff g = +-I
or tr g in {+-phi, +-phi'} (phi = (1+sqrt5)/2, phi' = (1-sqrt5)/2), since such
a g is diagonalizable with eigenvalues +- a primitive 5th root of unity.

We enumerate tr a, tr b, tr ab in Theta u {+-2} (Theta the four traces), build
a = [[x,1],[-1,0]], b = [[0,t],[-1/t,y]] with tr ab = z, and test all reduced
words of length <= Rmax numerically.  For each triple we report the largest R
for which the law holds on the R-ball, and whether the rep is reducible
(tr[a,b] = 2).

Usage: python3 sl2_traces.py Rmax
"""
import sys
import cmath
from itertools import product

PHI = (1 + 5 ** 0.5) / 2
PHIP = (1 - 5 ** 0.5) / 2
THETA = [PHI, -PHI, PHIP, -PHIP]
ALLOWED = THETA + [2.0, -2.0]
TOL = 1e-7


def mul(p, q):
    return ((p[0][0] * q[0][0] + p[0][1] * q[1][0], p[0][0] * q[0][1] + p[0][1] * q[1][1]),
            (p[1][0] * q[0][0] + p[1][1] * q[1][0], p[1][0] * q[0][1] + p[1][1] * q[1][1]))


def inverse(p):
    return ((p[1][1], -p[0][1]), (-p[1][0], p[0][0]))


def order5_psl(g):
    tr = g[0][0] + g[1][1]
    for t in THETA:
        if abs(tr - t) < TOL:
            return True
    if abs(tr - 2) < TOL or abs(tr + 2) < TOL:
        s = 1 if abs(tr - 2) < TOL else -1
        return (abs(g[0][0] - s) < TOL and abs(g[1][1] - s) < TOL
                and abs(g[0][1]) < TOL and abs(g[1][0]) < TOL)
    return False


def build(x, y, z):
    a = ((x, 1), (-1, 0))
    # tr(ab) with b = [[0,t],[-1/t,y]]: ab = [[-1/t, x t + y],[0, -t]] -> -1/t - t
    # so t + 1/t = -z
    disc = cmath.sqrt(z * z - 4)
    t = (-z + disc) / 2
    if abs(t) < 1e-12:
        return None
    b = ((0, t), (-1 / t, y))
    return a, b


def radius(a, b, Rmax):
    gens = [a, inverse(a), b, inverse(b)]
    inv = [1, 0, 3, 2]
    layer = [((), ((1, 0), (0, 1)))]
    for L in range(1, Rmax + 1):
        new = []
        for w, g in layer:
            for s in range(4):
                if w and inv[w[-1]] == s:
                    continue
                h = mul(g, gens[s])
                if not order5_psl(h):
                    return L - 1, w + (s,)
                new.append((w + (s,), h))
        layer = new
    return Rmax, None


def name(v):
    for lab, t in (("phi", PHI), ("-phi", -PHI), ("phi'", PHIP), ("-phi'", -PHIP), ("2", 2.0), ("-2", -2.0)):
        if abs(v - t) < TOL:
            return lab
    return "%.4f" % v


def main():
    Rmax = int(sys.argv[1])
    best = {}
    for x, y, z in product(ALLOWED, repeat=3):
        built = build(x, y, z)
        if built is None:
            continue
        a, b = built
        if not (order5_psl(a) and order5_psl(b) and order5_psl(mul(a, b))):
            continue
        c = mul(mul(a, b), mul(inverse(a), inverse(b)))
        comm_tr = (c[0][0] + c[1][1]).real
        r, w = radius(a, b, Rmax)
        best[(name(x), name(y), name(z))] = (r, round(comm_tr, 6), w)
    hist = {}
    for k, (r, ct, w) in best.items():
        hist.setdefault(r, []).append((k, ct, w))
    for r in sorted(hist):
        irr = [e for e in hist[r] if abs(e[1] - 2) > 1e-6]
        print(f"law holds exactly to radius {r}: {len(hist[r])} triples, {len(irr)} irreducible")
        for e in irr[:6]:
            print("   ", e)


if __name__ == "__main__":
    main()
