#!/usr/bin/env python3
"""Exact check of Proposition D in
research/artifacts/fpbs/docs/letter-saturated-morse-obstruction.md.

The per-letter sublevel system Sigma(T, k, rho, delta) consists of, for every letter s in T and level j >= 0
(u_j^s = removed s-mass of height > j, r_s = u_0^s the share of s, tau_s(j) = delta + sum_{t != s} u_j^t):

  (I1) u_0^s = r_s, u_j^s nonincreasing, u_j^s -> 0, sum_s r_s = 1 - delta;
  (I2) (1 - u_j^s) u_j^s <= k tau_s(j) / (1 - rho)                       [Lemmas 2' + 4]
  (I3) (k - 1) mu{ht_s = J} <= k (tau_s(J) + u_J^s)  for J >= 0,            [Lemma 3', refined]
       where mu{ht_s = 0} = 1 - r_s and mu{ht_s = J} = u_{J-1}^s - u_J^s for J >= 1.

Claim checked: with delta = 0, equal shares r_s = 1/|T| (|T| >= 2), the lockstep profile u_j^s = lam^j / |T|
satisfies (I1)-(I3) for every rho in [0, 1) and every lam in [lam_min, 1),
lam_min = (k - 1) / (k - 1 + k |T|).  Below lam_min, (I3) fails at J = 1 (sharpness of the profile family).

Also checked: the saturated bound of Theorem A, eps >= (k-1)(1-rho)/(6k^2), is positive for k >= 3, rho < 1,
so (I2)-(I3) with a single letter (|T| = 1, tau = delta) are what the w8 argument uses; the lockstep family
does not exist at |T| = 1 because (I2) then reads (1-u)u <= k delta/(1-rho) with no u on the right.

Exact rational arithmetic; the profile is geometric, so (I2) and (I3) reduce to finitely many checks
(J = 0 and one generic J >= 1, which scale by lam^J), but we also check the first 60 levels literally.
Exit 0 iff all checks pass.
"""
from fractions import Fraction as F
import sys

LEVELS = 60


def check(T, k, rho, lam):
    """Return (ok, first_failure) for the lockstep profile."""
    delta = F(0)
    u = [lam ** j / T for j in range(LEVELS + 1)]  # same for every letter
    r = u[0]
    for j in range(LEVELS + 1):
        tau = delta + (T - 1) * u[j]
        # (I2)
        if (1 - u[j]) * u[j] > k * tau / (1 - rho):
            return False, ("I2", j)
        # (I3)
        thick = (1 - r) if j == 0 else (u[j - 1] - u[j])
        if (k - 1) * thick > k * (tau + u[j]):
            return False, ("I3", j)
        if j >= 1 and u[j] > u[j - 1]:
            return False, ("I1", j)
    return True, None


def main():
    bad = 0
    rhos = [F(0), F(1, 3), F(9, 10), F(99, 100)]
    for T in (2, 3, 4, 6):
        for k in range(2, 11):
            lam_min = F(k - 1, k - 1 + k * T)
            for rho in rhos:
                for lam in (lam_min, (lam_min + 1) / 2, F(999, 1000)):
                    ok, why = check(T, k, rho, lam)
                    if not ok:
                        print("FAIL lockstep", T, k, rho, lam, why)
                        bad += 1
                # sharpness: just below lam_min, (I3) must fail at J = 1
                ok, why = check(T, k, F(0), lam_min * F(999, 1000))
                if ok or why[0] != "I3" or why[1] != 1:
                    print("FAIL sharpness", T, k, why)
                    bad += 1
    # Theorem A constant positive for k >= 3, rho < 1
    for k in range(3, 11):
        for rho in rhos:
            c = F(k - 1) * (1 - rho) / (6 * k * k)
            if not c > 0:
                print("FAIL constant", k, rho)
                bad += 1
    print("lockstep barrier checks:", "all passed" if bad == 0 else f"{bad} failures")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
