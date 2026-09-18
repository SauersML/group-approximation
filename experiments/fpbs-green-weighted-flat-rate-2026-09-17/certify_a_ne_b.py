#!/usr/bin/env python3
"""Exact-rational certificate that A != B on (Z/2)^{*k} * (Z/3)^{*m}.

Notation (see research/fpbs-flat-rate-point-exceeds-l2-point-on-free-products.md):
  q(p) = p + (1-p) p^2                        K_3 two-point function
  Phi(u2,u3) = k u2/(1+u2) + m u3/(1+u3)       reduced-word sum criterion
  p_2 : unique root in (0,1) of Phi(p^2, 2 q(p)^2) = 1
  A = (log a(R)^2, log 2F(R)^2),  B = (log p_2^2, log 2 q(p_2)^2)

If A = B then a(R) = p_2 and F(R) = q(p_2), and this pair satisfies both
first-passage equations at the same z = R:
  z1(a,F) = d a / (1 + ((k-1) a + 2 m F) a)
  z2(a,F) = d F / (1 + F + (k a + 2 (m-1) F) F)
so z1(p_2, q(p_2)) = z2(p_2, q(p_2)).  We bracket p_2 in a rational interval
[lo, hi] by exact bisection and enclose z1 and z2 over it using monotonicity
(q is nondecreasing on [0,1], numerators and denominators are nondecreasing
in p).  Disjoint enclosures prove z1 != z2, hence A != B.

No floating point is used.  Run: python3 certify_a_ne_b.py
"""
from fractions import Fraction as Fr


def q(p):
    return p + (1 - p) * p * p


def phi(u2, u3, k, m):
    return k * u2 / (1 + u2) + m * u3 / (1 + u3)


def p2_bracket(k, m, steps=80):
    lo, hi = Fr(0), Fr(1)
    f = lambda p: phi(p * p, 2 * q(p) ** 2, k, m) - 1
    assert f(lo) < 0 < f(hi)
    for _ in range(steps):
        mid = (lo + hi) / 2
        # limit denominator growth: round mid to a dyadic rational (bisection is dyadic anyway)
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    assert f(lo) < 0 < f(hi)
    return lo, hi


def z1_enclosure(lo, hi, k, m):
    d = k + 2 * m
    num_lo, num_hi = d * lo, d * hi
    den_lo = 1 + ((k - 1) * lo + 2 * m * q(lo)) * lo
    den_hi = 1 + ((k - 1) * hi + 2 * m * q(hi)) * hi
    return num_lo / den_hi, num_hi / den_lo


def z2_enclosure(lo, hi, k, m):
    d = k + 2 * m
    Ql, Qh = q(lo), q(hi)
    num_lo, num_hi = d * Ql, d * Qh
    den_lo = 1 + Ql + (k * lo + 2 * (m - 1) * Ql) * Ql
    den_hi = 1 + Qh + (k * hi + 2 * (m - 1) * Qh) * Qh
    if m == 0:
        raise ValueError("m >= 1 required")
    # k*a + 2(m-1)F >= 0 for m >= 1, so the denominator is nondecreasing
    return num_lo / den_hi, num_hi / den_lo


def main():
    cases = [(2, 1), (3, 1), (1, 2), (2, 2), (4, 1), (1, 1)]
    all_ok = True
    for k, m in cases:
        lo, hi = p2_bracket(k, m)
        a1, b1 = z1_enclosure(lo, hi, k, m)
        a2, b2 = z2_enclosure(lo, hi, k, m)
        disjoint = b1 < a2 or b2 < a1
        print(f"k={k} m={m}: p_2 in [{float(lo):.15f}, {float(hi):.15f}]  "
              f"z1 in [{float(a1):.12f}, {float(b1):.12f}]  "
              f"z2 in [{float(a2):.12f}, {float(b2):.12f}]  A != B certified: {disjoint}")
        all_ok = all_ok and disjoint
    print("all certified:", all_ok)


if __name__ == "__main__":
    main()
