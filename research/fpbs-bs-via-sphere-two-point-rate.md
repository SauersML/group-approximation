---
rg: 2
id: fpbs-bs-via-sphere-two-point-rate
kind: route
title: Bound the walk connectivity rate by the sphere two-point rate and read off nonuniqueness
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-sphere-two-point-rate-below-arccosh-universal
  - fpbs-sphere-two-point-rate-bounds-walk-rate
artifacts:
  - research/artifacts/fpbs/docs/gauge-certificates-and-sphere-rate-2026-09-17.md
---

**The route.**

1. Kernel (G) supplies `p > p_c` with `g(p) < arccosh(1/rho)`.
2. Theorem 3.2 gives `lambda(p) <= rho cosh g(p) < 1`.
3. Corollary 3.3: the bound persists below `p`, and uniqueness would force
   `lambda = 1`. So `p_u >= p > p_c`.

**Load-bearing premise.** Only (G). The implication is established.
