#!/usr/bin/env python3
"""Exact certificate for the continuum lower bound  ||P|| >= J_lo(h, k) / 2.

Input: a histogram JSON with float vectors h, k (any provenance).  They are rounded to positive
integers hI_i = max(1, round(h_i 2^60)), kI_i likewise, and the certificate uses the exact rational
probability vectors h_i = hI_i / sum(hI), k_i = kI_i / sum(kI).  With H, K the cdfs (H_0 = K_0 = 0),
    J = (sum_i sqrt(h_i k_i))^2 + sum_i I_i,   I_i = int_0^1 sqrt(a_i + b_i s) ds,
    a_i = h_i (h_i K_{i-1} + k_i H_{i-1}),   b_i = 2 h_i^2 k_i.
Each I_i is bounded below by the larger of the trapezoid value (sqrt(x) + sqrt(y))/2 (concavity) and
the closed form (2/3)(x + sqrt(xy) + y)/(sqrt x + sqrt y), x = a_i + b_i, y = a_i, with its numerator
rounded down and denominator rounded up.  Square roots use s = isqrt(floor(q 4^P)), so
s / 2^P <= sqrt(q) <= (s + 1) / 2^P for an exact Fraction q; all further operations are monotone on
nonnegatives, so the printed J_low <= J exactly.
Pure Python (fractions, math.isqrt).  Usage: certify_continuum.py hist.json [target]
"""
import sys, json, math
from fractions import Fraction

P = 256
ONE = 1 << P


def sqrt_lo(q):
    """Integer s with s / 2^P <= sqrt(q), q a nonnegative Fraction."""
    return math.isqrt((q.numerator << (2 * P)) // q.denominator)


def certify(h, k):
    hI = [max(1, round(x * 2 ** 60)) for x in h]
    kI = [max(1, round(x * 2 ** 60)) for x in k]
    Sh, Sk = sum(hI), sum(kI)
    hq = [Fraction(x, Sh) for x in hI]
    kq = [Fraction(x, Sk) for x in kI]
    bc1 = sum(sqrt_lo(hq[i] * kq[i]) for i in range(len(hq)))  # scaled by 2^P
    H = K = Fraction(0)
    t2 = 0  # scaled by 2^(P+1)
    for hi, ki in zip(hq, kq):
        a = hi * (hi * K + ki * H)
        b = 2 * hi * hi * ki
        x, y = a + b, a
        sx, sy = sqrt_lo(x), sqrt_lo(y)
        trap = sx + sy  # 2 * trapezoid, a lower bound of 2 * I_i (concavity)
        # exact I_i = (2/3)(x + sqrt(xy) + y)/(sqrt x + sqrt y): numerator rounded down, denominator up
        num = (x + y) * ONE * ONE + sx * sy          # <= (x + sqrt(xy) + y) 4^P
        den = (sx + 1) + (sy + 1)                    # >= (sqrt x + sqrt y) 2^P
        exact2 = math.floor(Fraction(4, 3) * num / den)  # <= 2 I_i 2^P
        t2 += max(trap, exact2)
        H += hi
        K += ki
    assert H == 1 and K == 1
    J_low = Fraction(bc1 * bc1, ONE * ONE) + Fraction(t2, 2 * ONE)
    return J_low, hI, kI


def main():
    d = json.load(open(sys.argv[1]))
    J_low, hI, kI = certify(d['h'], d['k'])
    out = {'n': len(hI), 'J_low_decimal': '%.12f' % float(J_low), 'normP_low_decimal': '%.12f' % float(J_low / 2),
           'J_low_num': str(J_low.numerator), 'J_low_den': str(J_low.denominator), 'hI': hI, 'kI': kI}
    if len(sys.argv) > 2:
        target = Fraction(sys.argv[2])
        out['target_normP'] = str(target)
        out['J_low/2 > target'] = J_low / 2 > target
    print(json.dumps(out))
    print(json.dumps({k: v for k, v in out.items() if k not in ('J_low_num', 'J_low_den', 'hI', 'kI')}),
          file=sys.stderr)


if __name__ == '__main__':
    main()
