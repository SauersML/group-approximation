#!/usr/bin/env python3
"""Calibration for the zero-free reframing of fpbs-pivotal-budget-universal.

Part 1. On the 3-regular tree T_3 (p_c = 1/2, p_(2->2) = 1/sqrt(2)) the
walk-averaged connectivity is a_n(z) = E[z^{|X_n|}] for simple random walk X_n.
It does not depend on the ball radius R >= n. We count zeros of a_n inside
discs centred on the real axis by the argument principle and record sup |a_n|
on the disc boundary. The growth hypothesis (G) holds with M = 0 for |z| <= 1.

Expected: no zeros in |z - 1/2| < 0.15, a disc containing p_c; zeros pinch
near p_(2->2) = 0.7071, where the flat rate lambda = rho ends.

Part 2. The parallel-routes toy tau(z) = 1 - (1 - z^L)^m with m = 2^L.
It has zeros approaching the real point 1/2 and its modulus on a fixed
circle around 1/2 grows without bound in L. This isolates the growth step (G).
"""
import cmath
import math


def dist_law(n, d=3):
    v = [1.0]
    for _ in range(n):
        w = [0.0] * (len(v) + 1)
        for k, pk in enumerate(v):
            if pk == 0.0:
                continue
            if k == 0:
                w[1] += pk
            else:
                w[k + 1] += pk * (d - 1) / d
                w[k - 1] += pk / d
        v = w
    return v


def evalpoly(c, z):
    s = 0j
    for ck in reversed(c):
        s = s * z + ck
    return s


def winding(f, c0, r, m=6000):
    tot, prev, sup = 0.0, None, 0.0
    for j in range(m + 1):
        z = c0 + r * cmath.exp(2j * math.pi * j / m)
        val = f(z)
        sup = max(sup, abs(val))
        ang = cmath.phase(val)
        if prev is not None:
            da = ang - prev
            while da > math.pi:
                da -= 2 * math.pi
            while da < -math.pi:
                da += 2 * math.pi
            tot += da
        prev = ang
    return round(tot / (2 * math.pi)), sup


def main():
    print("T_3 simple random walk, a_n(z) = E z^|X_n|")
    print("   n  zeros|z-.5|<.15  zeros|z-.5|<.25  zeros|z-.7071|<.05  sup|a_n| on |z-.5|=.25")
    for n in (20, 40, 80, 120, 160, 200):
        c = dist_law(n)
        f = lambda z, c=c: evalpoly(c, z)
        z1, _ = winding(f, 0.5, 0.15)
        z2, s2 = winding(f, 0.5, 0.25)
        z3, _ = winding(f, 1 / math.sqrt(2), 0.05)
        print(f"{n:4d}  {z1:15d}  {z2:15d}  {z3:17d}  {s2:.3e}")
    print()
    print("parallel-routes toy tau(z) = 1-(1-z^L)^m, m = 2^L, circle |z-0.5| = 0.1")
    for L in (4, 8, 12, 16):
        m = 2 ** L
        f = lambda z, L=L, m=m: 1 - (1 - z ** L) ** m
        zc, sup = winding(f, 0.5, 0.1, m=40000)
        print(f"L={L:3d} m={m:7d} zeros inside={zc:6d}  sup|tau| on circle={sup:.3e}")


if __name__ == "__main__":
    main()
