#!/usr/bin/env python3
"""Calibration of the l^q two-point bound on the regular tree T_d.

On T_d, tau_p(o,x) = p^|x| and a_n(p) = E[p^{|X_n|}] for simple random walk X.
The script computes a_n(p) exactly by the distance chain (d-regular tree:
from 0 go to 1; from r>=1 go to r+1 w.p. (d-1)/d and to r-1 w.p. 1/d), then
checks, for every q >= 2 with sum_x tau_p(o,x)^q < infinity, the lemma

    a_n(p) <= rho^(2n/q),   rho = 2 sqrt(d-1)/d,

with constant 1, and in particular a_n(p) <= rho^n for p <= p_2 = (d-1)^(-1/2).
It also prints the l^q thresholds p_q = (d-1)^(-1/q) and the n-th roots.
Exit code 0 iff every checked inequality holds.
"""
import math
import sys
from fractions import Fraction


def walk_rate_terms(d, p, N):
    """Return [a_0..a_N] with a_n = E p^{|X_n|} on T_d, computed exactly in floats."""
    dist = {0: 1.0}
    out = []
    for n in range(N + 1):
        out.append(sum(w * p ** r for r, w in dist.items()))
        new = {}
        for r, w in dist.items():
            if r == 0:
                new[1] = new.get(1, 0.0) + w
            else:
                new[r + 1] = new.get(r + 1, 0.0) + w * (d - 1) / d
                new[r - 1] = new.get(r - 1, 0.0) + w / d
        dist = new
    return out


def lq_threshold_q(d, p):
    """q_c(p) = inf{q: sum_r d(d-1)^(r-1) p^(q r) < inf} = log(d-1)/log(1/p)."""
    return math.log(d - 1) / math.log(1.0 / p)


def main():
    ok = True
    N = 400
    for d in (3, 4, 6):
        rho = 2 * math.sqrt(d - 1) / d
        pc = 1.0 / (d - 1)
        p2 = (d - 1) ** -0.5
        print(f"T_{d}: rho={rho:.6f} p_c={pc:.6f} p_2=p_22={p2:.6f}",
              "p_q for q=2.5,3,4:", [round((d - 1) ** (-1 / q), 6) for q in (2.5, 3, 4)])
        for p in (pc, 0.5 * (pc + p2), p2, 0.5 * (p2 + 1), 0.95):
            a = walk_rate_terms(d, p, N)
            qc = lq_threshold_q(d, p)
            # the lemma applies for every q > q_c; the sharpest exponent is 2/max(2,q_c)
            expo = 2.0 / max(2.0, qc)
            worst = max(a[n] / rho ** (expo * n) for n in range(1, N + 1))
            # strict q slightly above q_c: bound rho^(2n/q) with q = max(2, qc)*(1+1e-9)
            flag = worst <= 1.0 + 1e-9
            ok &= flag
            # exact rate on T_d: rho for p <= p_2, ((d-1)p + 1/p)/d for p >= p_2
            tree_exact = rho if p <= p2 else ((d - 1) * p + 1 / p) / d
            print(f"  p={p:.5f} q_c={qc:.4f} bound rate rho^(2/max(2,q_c))={rho**expo:.6f}"
                  f" exact lambda={tree_exact:.6f} a_N^(1/N)={a[N]**(1/N):.6f}"
                  f" max_n a_n/bound^n={worst:.6f} {'OK' if flag else 'FAIL'}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
