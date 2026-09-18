#!/usr/bin/env python3
"""Exact conditional random-walk pivotal counts on the d-regular tree T_d.

On T_d = Cay((Z/2)^(*d)) the event E_(n,R) (R>=n) is "the geodesic from e to
X_n is open", and every edge of that geodesic is an open pivotal edge, so

    E_p[N_(n,R) | E_(n,R)] = sum_k k w_k p^k / sum_k w_k p^k,
    w_k = P(|X_n| = k)   (simple random walk).

This script computes w_k exactly with rational arithmetic (radial chain:
0 -> 1 w.p. 1; k -> k+1 w.p. (d-1)/d, k -> k-1 w.p. 1/d) and prints the
count divided by n below, at, and above p_(2->2) = 1/sqrt(d-1).
It also checks the two inequalities used in the proof:
    mu^n(e) <= rho^n,  rho = 2 sqrt(d-1)/d, and
    sigma_k(n) := w_k / (rho^n (d-1)^(k/2)) <= d/(d-1).
Run: python3 tree_pivotal_counts.py
"""
from fractions import Fraction
import math


def radial_law(d, n):
    w = {0: Fraction(1)}
    up, down = Fraction(d - 1, d), Fraction(1, d)
    for _ in range(n):
        nw = {}
        for k, v in w.items():
            if k == 0:
                nw[1] = nw.get(1, 0) + v
            else:
                nw[k + 1] = nw.get(k + 1, 0) + v * up
                nw[k - 1] = nw.get(k - 1, 0) + v * down
        w = nw
    return w


def count(w, p):
    num = sum(k * float(v) * p ** k for k, v in w.items())
    den = sum(float(v) * p ** k for k, v in w.items())
    return num / den


def main():
    d = 3
    thr = 1 / math.sqrt(d - 1)
    rho = 2 * math.sqrt(d - 1) / d
    beta = d / (d - 1)
    print(f"d={d}  p_c=1/(d-1)={1/(d-1):.4f}  p_2to2={thr:.4f}")
    print(" n    p=0.8*thr   p=thr   p=1.2*thr   (count; count/n above)")
    for n in (20, 40, 80, 160, 320):
        w = radial_law(d, n)
        assert abs(sum(float(v) for v in w.values()) - 1) < 1e-12
        # proof inequalities
        assert float(w.get(0, 0)) <= rho ** n * (1 + 1e-12)
        for k, v in w.items():
            sigma = float(v) / (rho ** n * (d - 1) ** (k / 2))
            assert sigma <= beta * (1 + 1e-9), (n, k, sigma)
        lo, mid, hi = count(w, 0.8 * thr), count(w, thr), count(w, 1.2 * thr)
        print(f"{n:4d}  {lo:9.4f}  {mid:8.4f}  {hi:9.4f}  {hi/n:.4f}")
    print("bounded below threshold, ~sqrt(n) at threshold, linear above")


if __name__ == "__main__":
    main()
