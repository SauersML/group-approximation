#!/usr/bin/env python3
"""Exact rational check of the oriented second-moment / non-backtracking criterion
for tree-projected Cayley graphs (claim fpbs-tree-projected-rank-three-strict-thresholds).

Parameters: rank n >= 2, least multiplicity mlo, largest multiplicity mhi,
vertical count v, degree d = |S|.

  p_o  = 1 / ( (2n-1) mlo - (mlo-1)^2 / ((2n-2) mlo^2 + mlo - 1) )     (p_c <= p_o)
  lam  = v + 2 mhi sqrt(2n-1)                                           (||A|| <= lam)
  p*   = smallest positive root of (d-1) p^2 - lam p + 1                (p_u >= p*)

Criterion: p_o < p*.  Checked exactly: with lamU a rational upper bound for lam,
  f(p_o) = (d-1) p_o^2 - lamU p_o + 1 > 0  and  2 (d-1) p_o < lamU
imply p_o < p*(lamU) <= p*(lam).  (p* is decreasing in lam.)
Also calibration: mlo = 1 gives p_o = 1/(2n-1), the tree threshold.
"""
from fractions import Fraction as Fr
from math import isqrt
import sys

def sqrt_upper(k, den=10**6):
    # rational r with r >= sqrt(k), r - sqrt(k) < 1/den
    a = isqrt(k * den * den)
    if a * a < k * den * den:
        a += 1
    return Fr(a, den)

def p_o(n, m):
    b = 2 * n - 1
    return 1 / (Fr(b * m) - Fr((m - 1) ** 2, (b - 1) * m * m + m - 1))

def holds(n, mlo, mhi, v, d):
    po = p_o(n, mlo)
    lamU = v + 2 * mhi * sqrt_upper(2 * n - 1)
    f = (d - 1) * po * po - lamU * po + 1
    return f > 0 and 2 * (d - 1) * po < lamU

def pstar_float(lam, d):
    disc = lam * lam - 4 * (d - 1)
    if disc < 0:
        return (d - 1) ** -0.5
    return (lam - disc ** 0.5) / (2 * (d - 1))

def main():
    # calibration m = 1
    for n in range(2, 8):
        assert p_o(n, 1) == Fr(1, 2 * n - 1)
    print("calibration: p_o(n,1) = 1/(2n-1) for n=2..7  OK")
    print()
    print("uniform multiplicity m on every letter, d = 2nm + v; largest v for which the criterion holds")
    print(" n  m   p_o        p*(v=0)    vmax")
    for n in range(2, 7):
        for m in range(1, 9):
            vmax = -1
            for v in range(0, 400):
                if holds(n, m, m, v, 2 * n * m + v):
                    vmax = v
                else:
                    break
            lam = 2 * m * (2 * n - 1) ** 0.5
            print(f"{n:2d} {m:2d}  {float(p_o(n,m)):.6f}  {pstar_float(lam, 2*n*m):.6f}  {vmax if vmax>=0 else 'none'}")
    print()
    examples = [
        ("rank-3 rigid {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(c,0),(c,1),(c,5),(1,1)}", 3, 3, 3, 2, 20),
        ("rank-3 rigid, no vertical generator {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(c,0),(c,1),(c,5)}", 3, 3, 3, 0, 18),
        ("rank-2 S_rig {(a,0),(a,1),(a,3),(b,0),(b,1),(b,4),(1,1)}", 2, 3, 3, 2, 14),
    ]
    for name, n, mlo, mhi, v, d in examples:
        po = p_o(n, mlo)
        lam = v + 2 * mhi * (2 * n - 1) ** 0.5
        print(f"{name}\n   p_o = {po} = {float(po):.6f}, p*(lam={lam:.4f}, d={d}) = {pstar_float(lam,d):.6f}, criterion exact: {holds(n,mlo,mhi,v,d)}")
    fails = [(n, m, v) for n in range(3, 9) for m in range(2, 2001) for v in (0, 2)
             if not holds(n, m, m, v, 2 * n * m + v)]
    print()
    print("exact check n=3..8, m=2..2000, v in {0,2}: failures", fails if fails else "none")
    # rank two never: show ratio for m up to 200, v = 0
    bad = [m for m in range(1, 201) if holds(2, m, m, 0, 4 * m)]
    print()
    print("rank two, v=0, m=1..200: criterion holds for", bad if bad else "no m")
    print("rank two asymptotics: p_o*m -> 1/3, p*(2 sqrt3 m, 4m)*m -> 1/(2 sqrt 3) = %.6f" % (1 / (2 * 3 ** 0.5)))

if __name__ == "__main__":
    main()
