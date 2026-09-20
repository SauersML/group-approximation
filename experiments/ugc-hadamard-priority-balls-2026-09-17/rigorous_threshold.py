"""Rigorous (exact rational) bracketing of the priority-ball threshold C*.

T(C) = int_0^{y0(C)} w_C(y) dy,  y0(C) = 1 - C (1 - e^{-1/2}),
w_C(y) = p(y) / (2 (C - (1-y)^4)),  p(y) = (1 - (1-y)^4)/y = 4 - 6y + 4y^2 - y^3.

w_C is positive and decreasing on [0,1] for C >= 1 (p decreasing, C-(1-y)^4
increasing), and T is decreasing in C.  C* is the root of T(C) = 1/4.
Left sums over-estimate, right sums under-estimate; e^{-1/2} is bracketed by
Taylor partial sums of an alternating series.  All arithmetic is Fraction.
Usage: python3 rigorous_threshold.py C_lo C_hi N
Proves T(C_lo) > 1/4 > T(C_hi), hence C_lo < C* < C_hi.
"""
import sys
from fractions import Fraction as F


def exp_neg_half():
    """Return (lo, hi) with lo < e^{-1/2} < hi (alternating series)."""
    x, term, s, n = F(-1, 2), F(1), F(0), 0
    parts = []
    while n < 30:
        s += term
        parts.append(s)
        n += 1
        term = term * x / n
    lo, hi = min(parts[-1], parts[-2]), max(parts[-1], parts[-2])
    D = 10 ** 15  # outward rounding to short rationals
    return F((lo * D).numerator // (lo * D).denominator, D), \
        F(-((-hi * D).numerator // (-hi * D).denominator), D)


def w(C, y):
    q = (1 - y) ** 4
    p = 4 - 6 * y + 4 * y ** 2 - y ** 3
    return p / (2 * (C - q))


def T_bounds(C, N):
    elo, ehi = exp_neg_half()
    y0_lo, y0_hi = 1 - C * (1 - elo), 1 - C * (1 - ehi)
    # lower bound: right-endpoint sum on [0, y0_lo]
    h = y0_lo / N
    lower = sum(w(C, h * j) for j in range(1, N + 1)) * h
    h = y0_hi / N
    upper = sum(w(C, h * j) for j in range(0, N)) * h
    return lower, upper


if __name__ == '__main__':
    C_lo, C_hi, N = F(sys.argv[1]), F(sys.argv[2]), int(sys.argv[3])
    lo_lo, lo_hi = T_bounds(C_lo, N)
    hi_lo, hi_hi = T_bounds(C_hi, N)
    print("T(C_lo) in [%.8f, %.8f]" % (lo_lo, lo_hi))
    print("T(C_hi) in [%.8f, %.8f]" % (hi_lo, hi_hi))
    ok = lo_lo > F(1, 4) and hi_hi < F(1, 4)
    print("certified C_lo < C* < C_hi:", ok, float(C_lo), float(C_hi))
