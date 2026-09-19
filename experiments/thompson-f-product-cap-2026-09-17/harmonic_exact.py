#!/usr/bin/env python3
"""Harmonic size law nu_M(m) = 1/(m H_M), m = 1..M (float check of the closed form, scouting only).

(nu*nu)(j) = (2 H_{j-1}) / (j H_M^2), so
    Phi(nu_M, nu_M) = 1 + sum_{j=2}^M sqrt(2 H_{j-1}) / (j H_M^{3/2})  ->  1 + 2 sqrt(2)/3.
Prints the closed form for M = 2^e; finite_m_check.py on hist_exact_n1.json computes the same
quantity by FFT convolution (finite_m_check_n1.out), and the two agree to float precision.
"""
import math, json
for e in (8, 12, 16, 20, 22):
    M = 1 << e
    H = 0.0; s = 0.0
    for j in range(1, M + 1):
        if j >= 2:
            s += math.sqrt(2 * H) / j
        H += 1.0 / j
    print(json.dumps({'e': e, 'Phi': 1 + s / H ** 1.5, 'limit': 1 + 2 * math.sqrt(2) / 3}), flush=True)
