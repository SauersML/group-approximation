---
rg: 2
id: fpbs-integrated-sensitivity-via-lq-two-point
kind: route
title: Squeeze the walk rate between rho and rho to the 2/q using l^q summability of the supercritical two-point function
target: fpbs-integrated-sensitivity-universal
requires:
  - fpbs-lq-two-point-bounds-walk-rate
  - fpbs-two-point-lq-threshold-gap-universal
  - fpbs-integrated-pivotal-rate-identity
artifacts:
  - research/artifacts/fpbs/docs/lq-two-point-walk-rate-2026-09-17.md
---

**The route** (Theorem 4.2 of the artifact).

1. `lambda` is nondecreasing and satisfies `lambda >= rho`.
2. Given `q > 2`, [Q] supplies `p' in (p_c, p_q)`. By
   `fpbs-lq-two-point-bounds-walk-rate`,
   `rho <= lambda(p) <= rho^(2/q)` on `(p_c, p']`.
3. Letting `q` decrease to 2 gives `lambda(p) -> rho` as `p` decreases to
   `p_c`.
4. By the rate identity (6.4), this is (IS).

**Load-bearing premise.** Only [Q], `fpbs-two-point-lq-threshold-gap-universal`.
It is implied by the operator gap `p_c < p_{2->2}`, with no
operator boundedness required.
