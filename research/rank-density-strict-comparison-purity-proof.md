---
rg: 2
id: rank-density-strict-comparison-purity-proof
kind: route
title: Divide a continuous tracial sandwich by k plus one half and absorb the error by comparison
target: rank-density-and-strict-comparison-give-purity
requires: []
artifacts:
  - research/artifacts/toms-winter-rank-density-firewall-2026-09-11.md
---

Strict comparison gives almost unperforation of `Cu(A)` for simple exact `A`,
so only almost divisibility needs proof.

Let `x = [a]` with `a in (A tensor K)_+`, let `x' << x` be nonzero, and let `k`
be given.

1. Choose `eps > 0` with `x' <= [(a - 2eps)_+]`, and `b in M_n(A)_+` with
   `||a - b|| < eps/2`.  Kirchberg--Rordam norm perturbation gives
   `x' <= [(b - eps)_+]` and `[(b - eps/2)_+] <= x`.
2. Take a continuous `phi` on `[0, infty)` with `phi = 0` on `[0, eps/2]` and
   `phi = 1` on `[eps, infty)`, and put `h(tau) = tau(phi(b))`.  This is a
   continuous affine function with

   ```text
   d(x') <= d((b - eps)_+) <= h <= d((b - eps/2)_+) <= d(x).
   ```

3. All traces are faithful and `tau -> d_tau((b - eps)_+)` is lower
   semicontinuous on compact `T(A)`, so `h >= c_0 > 0`.
4. By RD choose `y in M_infty(A)_+` with `|d(y) - h/(k + 1/2)| < eta`, where
   `eta < c_0/((2k+1)(k+1))`.  Then pointwise:

   ```text
   k d(y) < h <= d((b - eps/2)_+),
   (k+1) d(y) > h >= d((b - eps)_+).
   ```

5. Strict comparison inside `M_infty(A)` yields
   `k y <= [(b - eps/2)_+] <= x` and `x' <= [(b - eps)_+] <= (k+1) y`.

So `Cu(A)` is almost divisible, and with almost unperforation `A` is pure.
The arithmetic is written out in Section 2 of the linked artifact.
