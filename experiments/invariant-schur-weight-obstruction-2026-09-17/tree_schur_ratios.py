#!/usr/bin/env python3
"""Calibration for fpbs-invariant-schur-weights-cannot-certify-critical-l2.

Graph: the 3-regular tree T_3 = Cay(Z/2*Z/2*Z/2), p_c = 1/2, tau(u,v) = 2^(-d(u,v)).
For three kinds of weight h we compute the Schur ratio (T h)(v)/h(v), truncating the
sum over u at distance <= J, exactly by counting vertices by type.

* constant weight h = 1 (the Gamma-fixed point of W_C, invariant measure delta_1):
  ratio = truncated chi_{p_c} = 1 + 3J/2 -> infinity. The obstruction predicts divergence.
* Busemann weight h = 2^(-b/2) (projectively fixed by the stabilizer of an end, a cyclic
  subgroup of Gamma that is not coamenable): bounded ratio. The obstruction does not apply.
* radial weight h(v) = (1+|v|) 2^(-|v|/2) (fixed only by the trivial vertex stabilizer in
  Gamma): bounded ratio. The obstruction does not apply.

Run: python3 tree_schur_ratios.py
"""
from fractions import Fraction


def constant_ratio(J):
    # vertices at distance j from v: 1 if j = 0, else 3*2^(j-1)
    return sum((Fraction(1) if j == 0 else Fraction(3 * 2 ** (j - 1))) / 2 ** j
               for j in range(J + 1))


def busemann_ratio(J):
    # From v: up k steps toward the end, then down l steps without retracing.
    # k = 0: 2^l vertices below v at depth l. k >= 1: 1 vertex if l = 0, else 2^(l-1).
    # b(u) - b(v) = l - k, d(u,v) = k + l, h(u)/h(v) = 2^((k-l)/2).
    s = 0.0
    for k in range(J + 1):
        for l in range(J + 1 - k):
            cnt = 2 ** l if k == 0 else (1 if l == 0 else 2 ** (l - 1))
            s += cnt * 2.0 ** (-(k + l)) * 2.0 ** ((k - l) / 2)
    return s


def radial_ratio(n, J):
    # v at level n >= 0 from the root o. u is reached by going up k <= n steps, then
    # down j steps into a branch avoiding the child toward v. |u| = n-k+j, d = k+j.
    def h(m):
        return (1 + m) * 2.0 ** (-m / 2)

    s = 0.0
    for k in range(min(n, J) + 1):
        for j in range(J + 1 - k):
            if j == 0:
                cnt = 1
            elif k == 0:
                cnt = 3 * 2 ** (j - 1) if n == 0 else 2 ** j
            elif k < n:
                cnt = 2 ** (j - 1)
            else:  # k == n: at the root, two other children
                cnt = 2 * 2 ** (j - 1)
            s += cnt * 2.0 ** (-(k + j)) * h(n - k + j)
    return s / h(n)


if __name__ == "__main__":
    for J in (10, 20, 40, 80):
        rad = max(radial_ratio(n, J) for n in range(61))
        print(f"J={J:3d}  constant ratio = {float(constant_ratio(J)):8.2f}   "
              f"Busemann ratio = {busemann_ratio(J):.6f}   "
              f"radial sup_(n<=60) ratio = {rad:.6f}")
