#!/usr/bin/env python3
"""Calibration of the short-torsion form of Kadison--Kaplansky on 1-marked groups.

A 1-marked group is Z or Z/n.  For a self-adjoint a = sum_{|k|<=K} a_k s^k in Q[i][F_1]
(a_{-k} = conj(a_k)), put f(theta) = sum a_k e^{ik theta} and L = sum |k||a_k| (a Lipschitz
constant of f).  In Z the spectrum of a is the interval f([0,2pi]); in Z/n it is
{f(2 pi j/n)} with uniform spectral measure.

Claim checked (Proposition 5 of kk-witness-counterexample-locus-is-marked-closed-proof):
if spec_{Z/n}(a) has points on both sides of a gap (c-eps, c+eps), then n <= pi L / eps.
Equivalently max_gap_halfwidth(n) * n <= pi L.  The script computes the largest
half-width of an internal spectral gap for every n <= NMAX and reports the worst ratio
n * eps_max(n) / (pi L), which must be <= 1.  It also reports, per polynomial, the largest n
that has any internal gap of half-width >= EPS_TEST, and checks it against pi L / EPS_TEST.
"""
import cmath, math, random

random.seed(20260917)
NMAX = 400
EPS_TEST = 0.25
worst = 0.0
fails = 0
for trial in range(300):
    K = random.randint(1, 4)
    coeffs = {0: complex(random.randint(-3, 3), 0)}
    for k in range(1, K + 1):
        c = complex(random.randint(-3, 3), random.randint(-3, 3))
        coeffs[k] = c
        coeffs[-k] = c.conjugate()
    L = sum(abs(k) * abs(v) for k, v in coeffs.items())
    if L == 0:
        continue
    last_gapped_n = 0
    for n in range(1, NMAX + 1):
        vals = sorted((sum(v * cmath.exp(1j * k * 2 * math.pi * j / n) for k, v in coeffs.items())).real
                      for j in range(n))
        gaps = [(vals[i + 1] - vals[i]) / 2 for i in range(len(vals) - 1)]
        eps_max = max(gaps) if gaps else 0.0
        ratio = n * eps_max / (math.pi * L)
        worst = max(worst, ratio)
        if ratio > 1 + 1e-9:
            fails += 1
        if eps_max >= EPS_TEST:
            last_gapped_n = n
    if last_gapped_n > math.pi * L / EPS_TEST + 1e-9:
        fails += 1
print(f"trials=300 NMAX={NMAX} worst n*eps_max/(pi L) = {worst:.4f} (must be <= 1); violations = {fails}")
