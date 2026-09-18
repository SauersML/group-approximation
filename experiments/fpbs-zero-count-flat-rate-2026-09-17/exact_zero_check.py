#!/usr/bin/env python3
"""Exact big-integer evaluation of a_n(z) = E z^{|X_n|} on T_3 at Gaussian
rationals z (9 decimal digits), confirming the zeros located by
tree_zero_count_linear.py without floating-point cancellation.

a_n(z) = sum_k P(|X_n| = k) z^k and 3^n P(|X_n| = k) = N_k are integers
(from 0 the walk steps up 3 ways; from k >= 1 up 2 ways and down 1 way).
For z = (a + b i)/S we compute S^n 3^n a_n(z) = sum_k N_k (a+bi)^k S^(n-k)
exactly by Horner and report log10 |a_n(z)| next to the no-cancellation scale
log10 max_k P(|X_n|=k) |z|^k.

Usage: python3 exact_zero_check.py 2000 0.732527580+0.058881712j 0.7325+0.0589j
Standard library only. n = 2000 takes about a minute per point.
"""
import math
import sys


def log10_int(x):
    x = abs(x)
    if x == 0:
        return -math.inf
    sh = max(0, x.bit_length() - 60)
    return math.log10(x >> sh) + sh * math.log10(2)


def main():
    n = int(sys.argv[1])
    pts = [complex(s) for s in sys.argv[2:]]
    N = [1]
    for _ in range(n):
        W = [0] * (len(N) + 1)
        for k, c in enumerate(N):
            if c == 0:
                continue
            if k == 0:
                W[1] += 3 * c
            else:
                W[k + 1] += 2 * c
                W[k - 1] += c
        N = W
    S = 10 ** 9
    for z in pts:
        a = int(round(z.real * S))
        b = int(round(z.imag * S))
        re, im = N[n], 0
        sp = 1
        for k in range(n - 1, -1, -1):
            sp *= S
            re, im = re * a - im * b + N[k] * sp, re * b + im * a
        lg = 0.5 * log10_int(re * re + im * im) - 9 * n - n * math.log10(3)
        absz = abs(z)
        lmax = max(log10_int(c) + k * math.log10(absz) for k, c in enumerate(N) if c)
        lscale = lmax - n * math.log10(3)
        print(f"n={n} z={z}: |z-1/2|={abs(z - 0.5):.6f} log10|a_n|={lg:.3f}, "
              f"log10 max_k P_k|z|^k={lscale:.3f}")


if __name__ == "__main__":
    main()
