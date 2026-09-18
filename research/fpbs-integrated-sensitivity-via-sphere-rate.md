---
rg: 2
id: fpbs-integrated-sensitivity-via-sphere-rate
kind: route
title: Squeeze the walk rate between rho and rho cosh of the sphere two-point rate
target: fpbs-integrated-sensitivity-universal
requires:
  - fpbs-sphere-two-point-rate-right-continuous-universal
  - fpbs-sphere-two-point-rate-bounds-walk-rate
artifacts:
  - research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md
---

**The route.**

1. `rho <= lambda(p) <= rho cosh(g_+(p))`.
2. If `g(p) -> 0` as `p` decreases to `p_c`, then `lambda(p) -> rho`.
3. By the rate identity (6.4), that is (IS).

**Load-bearing premise.** Only EG (Corollary 3.4 of the artifact).
