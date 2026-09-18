#!/usr/bin/env python3
"""Zeros of a_n(z) = E z^{|X_n|} on the regular tree T_d enter every domain
whose real trace passes p_lambda = (d-1)^(-1/2), at a linear rate in n.

Context: fpbs-sublinear-zero-interpolant-iff-flat-rate proves that if a family
F_n with |F_n|^(1/n) -> rho on a real interval, exponential growth, and o(n)
zeros on compacts of a symmetric simply connected domain U dominates a_n at a
real point p_+ of U, then lambda(p_+) = rho. On T_d, lambda(p) = phi(p) > rho for
p > p_lambda, where phi(z) = ((d-1) z + 1/z)/d. So every such U that contains
a real point beyond p_lambda must see a linear number of zeros of a_n. The
2026-09-17 script saw no zero in |z-1/2|<0.25 for n <= 200 (T_3); that disc
contains 0.75 > p_lambda = 0.7071, so zeros must appear for large n.

Numerics. Direct polynomial evaluation cancels catastrophically for large n,
so we use two exact identities for the distance chain Y_t = |X_t|:

  head:  a_(t+1) = phi a_t + (z - phi) r_t,   a_0 = 1,   r_t = P(Y_t = 0);
  tail:  a_n = -(z - phi) sum_(j>=n) r_j phi^(n-1-j)
         (valid in the inner component |z| < p_lambda, |phi| > rho, where the
          coefficient of phi^n vanishes because lambda = rho there).

Head is stable where |phi| <= rho (1 + O(1/n)) or the phi^n term dominates;
tail is stable in the inner component away from |phi| = rho. The zeros
accumulate on the curve Gamma = {|phi| = rho, |z| >= p_lambda}, which leaves
p_lambda at +-45 degrees. Predicted count on an arc of Gamma inside a disc:
n * (change of arg phi along the arc) / (2 pi), per branch.

Standard library plus numpy. Runs in about a minute.
"""
import math
import sys

import numpy as np

D = 3


def phi(z, d=D):
    return ((d - 1) * z + 1 / z) / d


def return_probs(J, d=D):
    """Scaled return probabilities rt_j = rho^(-j) P(|X_j| = 0), j < J.

    Unscaled r_j underflows (and sticks at subnormal values) for j beyond
    about 12000 on T_3, which corrupts the tail sum; an earlier version of
    this script failed at n = 4000 for that reason. We run the Doob-transformed
    chain vt[k] = rho^(-j) (d-1)^(-k/2) P(|X_j| = k): it moves k -> k+-1 with
    weight 1/2 for k >= 1 and 0 -> 1 with weight d/(2(d-1)), so every entry
    stays of polynomial size."""
    r = np.zeros(J)
    v = np.zeros(J + 3)
    v[0] = 1.0
    w01 = d / (2.0 * (d - 1))
    for j in range(J):
        r[j] = v[0]
        L = min(j + 2, J + 1)  # v[k] = 0 for k > j
        w = np.zeros_like(v)
        w[1] += w01 * v[0]
        w[2:L + 1] += 0.5 * v[1:L]   # k -> k+1 for k >= 1
        w[0:L - 1] += 0.5 * v[1:L]   # k -> k-1 for k >= 1
        v = w
    return r


def a_head(z, n, r, rho):
    """rho^(-n) a_n(z) from at_(t+1) = psi at_t + ((z - phi)/rho) rt_t."""
    f = phi(z)
    psi = f / rho
    c = (z - f) / rho
    a = np.ones_like(z)
    for t in range(n):
        a = psi * a + c * r[t]
    return a


def a_tail(z, n, r, rho, K):
    """rho^(-n) a_n(z) = -((z - phi)/rho) sum_k rt_(n+k) psi^(-1-k)."""
    f = phi(z)
    q = rho / f
    s = np.zeros_like(z)
    for k in range(K - 1, -1, -1):
        s = s * q + r[n + k]
    return -((z - f) / rho) * s * q


def a_eval(z, n, r, rho, K):
    """rho^(-n) a_n(z); zeros and winding numbers are those of a_n."""
    z = np.asarray(z, dtype=complex)
    f = phi(z)
    inner = np.abs(z) * math.sqrt(D - 1) < 1
    use_tail = inner & (np.abs(f) > rho * (1 + 15.0 / n))
    out = np.empty_like(z)
    if (~use_tail).any():
        out[~use_tail] = a_head(z[~use_tail], n, r, rho)
    if use_tail.any():
        out[use_tail] = a_tail(z[use_tail], n, r, rho, K)
    return out


def a_direct(z, n, d=D):
    v = [1.0]
    for _ in range(n):
        w = [0.0] * (len(v) + 1)
        for k, pk in enumerate(v):
            if k == 0:
                w[1] += pk
            else:
                w[k + 1] += pk * (d - 1) / d
                w[k - 1] += pk / d
        v = w
    s = 0j
    for c in reversed(v):
        s = s * z + c
    return s


def winding(vals):
    if not np.all(np.isfinite(vals)) or np.any(vals == 0):
        return None
    ph = np.angle(vals[1:] / vals[:-1])
    if np.max(np.abs(ph)) > 2.5:
        return None
    return int(round(ph.sum() / (2 * math.pi)))


def circle_count(c0, rad, n, r, rho, K, mult=40):
    m = mult * n
    t = np.linspace(0, 2 * math.pi, m + 1)
    z = c0 + rad * np.exp(1j * t)
    return winding(a_eval(z, n, r, rho, K))


def gamma_arc_alpha(c0, rad):
    """Largest alpha with z(alpha) = p_lambda * u(alpha) in the disc, where
    u + 1/u = 2 e^{i alpha}, |u| >= 1 (upper branch of Gamma)."""
    pl = 1 / math.sqrt(D - 1)
    lo, hi = 0.0, math.pi / 2
    def inside(al):
        w = complex(math.cos(al), math.sin(al))
        s = np.sqrt(w * w - 1)
        u = w + s if abs(w + s) >= 1 else w - s
        return abs(pl * u - c0) < rad
    if not inside(1e-9):
        return 0.0
    for _ in range(80):
        mid = (lo + hi) / 2
        if inside(mid):
            lo = mid
        else:
            hi = mid
    return lo


def main():
    rho = 2 * math.sqrt(D - 1) / D
    pl = 1 / math.sqrt(D - 1)
    ns = [int(x) for x in sys.argv[1:]] or [200, 500, 1000, 2000, 4000, 8000]
    Jmax = 6 * max(ns) + 10
    r = return_probs(Jmax)
    # sanity: head/tail formulas against direct evaluation at small n
    n0 = 60
    zs = np.array([0.5 + 0.2j, 0.3 + 0.1j, 0.72 + 0.05j, 0.1j + 0.6])
    ev = a_eval(zs, n0, r, rho, 4 * n0) * rho ** n0
    dv = np.array([a_direct(z, n0) for z in zs])
    print("check n=60: max rel err head/tail vs direct =",
          f"{np.max(np.abs(ev - dv) / np.abs(dv)):.2e}")
    discs = [(0.5, 0.25), (0.5, 0.24), (0.5, 0.15), (pl, 0.05), (pl, 0.1)]
    print(f"T_{D}: rho={rho:.6f}, p_lambda={pl:.6f}")
    head = "     n " + " ".join(f" |z-{c:.4f}|<{s:.2f}" for c, s in discs)
    print(head)
    for n in ns:
        K = 4 * n
        row = [circle_count(c, s, n, r, rho, K) for c, s in discs]
        print(f"{n:6d} " + " ".join(f"{str(x):>18s}" for x in row))
    print("predicted leading count (both branches), n * alpha_max / pi:")
    for c, s in discs:
        al = gamma_arc_alpha(c, s)
        print(f"  |z-{c:.4f}|<{s:.2f}: alpha_max={al:.5f}, "
              f"slope={al / math.pi:.6f} per n")


if __name__ == "__main__":
    main()
