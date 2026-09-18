#!/usr/bin/env python3
"""Sanity checks for expansion-certified-repetition-caps-deficit-ratio.

This script proves nothing. It checks numerically, on a grid, the three elementary
inequalities used by the route expansion-certified-repetition-caps-deficit-ratio-proof:

  (a) Bernoulli: 1 - (1 - psi)^n <= n psi                 for psi in [0,1], n >= 1;
  (b) round budget: (1-eta)^n >= 1 - eps', eps' <= 1/2  ==>  n eta <= 2 eps';
  (c) the final ratio bound: at every grid point obeying the source gate
      gamma <= 1536 eta/lam + 28 eta, and with psi = K gamma^2 + kappa lam gamma
      (clipped to 1), the deficit ratio (1 - (1-psi)^n)/eps' is at most
      2 K gamma^2/eta + 3184 kappa.

It also prints how large the certified ratio can get at the gate for the pure expansion
rate (K = 0), and the AKKSTV-type rate c lam g0 / ln(1/g0), g0 = min(gamma, 1/e).
"""
import math

def grid(lo, hi, m):
    return [lo * (hi / lo) ** (i / (m - 1)) for i in range(m)]

bad = 0
checked = 0
# (a)
for psi in [0.0] + grid(1e-9, 1.0, 60):
    for n in [1, 2, 3, 5, 10, 100, 10**4, 10**6]:
        checked += 1
        if 1 - (1 - psi) ** n > n * psi + 1e-12:
            bad += 1
print("(a) Bernoulli checks:", checked, "violations:", bad)

# (b)
bad = 0; checked = 0
for eta in grid(1e-7, 0.5, 50):
    for n in [1, 2, 5, 10, 100, 1000, 10**5]:
        eps = 1 - (1 - eta) ** n
        if eps <= 0.5:
            checked += 1
            if n * eta > 2 * eps + 1e-12:
                bad += 1
print("(b) round-budget checks:", checked, "violations:", bad)

# (c)
bad = 0; checked = 0; worst = 0.0
for K in [0.0, 1.0, 10.0]:
    for kappa in [0.01, 1.0, 5.0]:
        for eta in grid(1e-6, 0.1, 25):
            for lam in grid(1e-4, 2.0, 25):
                gmax = min(1.0, 1536 * eta / lam + 28 * eta)
                for gamma in grid(1e-8, gmax, 12):
                    psi = min(1.0, K * gamma ** 2 + kappa * lam * gamma)
                    for n in [1, 3, 10, 100, 10**4]:
                        eps = 1 - (1 - eta) ** n
                        if eps > 0.5 or eps <= 0:
                            continue
                        checked += 1
                        ratio = (1 - (1 - psi) ** n) / eps
                        bound = 2 * K * gamma ** 2 / eta + 3184 * kappa
                        worst = max(worst, ratio / bound)
                        if ratio > bound * (1 + 1e-9):
                            bad += 1
print("(c) ratio-bound checks:", checked, "violations:", bad,
      "max ratio/bound = %.4f" % worst)

# Pure expansion rate and AKKSTV-type rate at the gate.
for name, rate in [
    ("kappa lam gamma, kappa=1", lambda lam, g: min(1.0, lam * g)),
    ("AKKSTV c lam g0/ln(1/g0), c=1/2",
     lambda lam, g: min(1.0, 0.5 * lam * min(g, 1 / math.e) / math.log(1 / min(g, 1 / math.e)))),
]:
    best = 0.0
    for eta in grid(1e-6, 0.1, 30):
        for lam in grid(1e-4, 2.0, 30):
            g = min(1.0, 1536 * eta / lam + 28 * eta)
            psi = rate(lam, g)
            n = max(1, int(0.5 / eta))
            eps = 1 - (1 - eta) ** n
            if eps > 0.5:
                n -= 1
                eps = 1 - (1 - eta) ** n
            if n < 1:
                continue
            best = max(best, (1 - (1 - psi) ** n) / eps)
    print("max certified deficit ratio at the gate for rate [%s]: %.2f" % (name, best))
