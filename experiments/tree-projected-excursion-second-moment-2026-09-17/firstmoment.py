#!/usr/bin/env python3
"""First-moment obstruction for depth-one excursion ensembles in rank two (exact rationals).

Ensemble class X: trails with N tree steps along a reduced word t_1..t_N that, in each of
the N+1 slots (before the first step, between steps, after the last step), make any
finite sequence of depth-one excursions (any of the 4 letters, u != u' in D_e).  Counting
edge sequences with no constraint beyond u != u' over-counts the trails, so

    E Z_N <= 4 3^(N-1) (m p)^N (1 - q)^(-(N+1)),   q = 4 m (m-1) p^2,

and E Z_N -> 0 whenever 3 m p < 1 - q, i.e. 4 m (m-1) p^2 + 3 m p < 1.  Then
P(Z_N > 0) <= E Z_N -> 0, so no second moment over X gives theta(p) > 0.

Adding vertical steps (1, +-1) inside slots (v = 2) changes q to q + 2p.
For each m and v = 2 the script compares the first-moment root with p*(m, 2).
"""
from fractions import Fraction as F
from math import isqrt

S3_LO, S3_UP = F(17320, 10000), F(17321, 10000)
assert S3_LO ** 2 < 3 < S3_UP ** 2


def sqrt_bounds(x, q=10 ** 9):
    r = isqrt(int(x * q * q))
    return F(r, q), F(r + 1, q)


def pstar_bounds(m, v):
    d = 4 * m + v
    lo_lam, up_lam = v + 2 * m * S3_LO, v + 2 * m * S3_UP
    lo_sq = sqrt_bounds(lo_lam ** 2 - 4 * (d - 1))[0]
    up_sq = sqrt_bounds(up_lam ** 2 - 4 * (d - 1))[1]
    return F(2) / (up_lam + up_sq), F(2) / (lo_lam + lo_sq)


def root(f, lo=F(0), hi=F(1, 2), it=60):
    for _ in range(it):
        mid = (lo + hi) / 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi


for m in range(3, 9):
    plo, pup = pstar_bounds(m, 2)
    fX = lambda p: 4 * m * (m - 1) * p * p + 3 * m * p - 1
    # vertical steps: 3 m p < 1 - q - 2p
    fV = lambda p: 4 * m * (m - 1) * p * p + 2 * p + 3 * m * p - 1
    rX = root(fX)
    rV = root(fV)
    deadX = fX(pup) < 0      # first moment of X decays at every p <= p*
    print('m=%d v=2: p* in [%.6f, %.6f]; X root %.6f -> %s; X+vertical root %.6f -> %s'
          % (m, float(plo), float(pup), float(rX[0]),
             'DEAD (E Z_N -> 0 for all p <= p*)' if deadX else 'not excluded',
             float(rV[0]), 'below p*' if fV(plo) > 0 else 'not below p*'))
