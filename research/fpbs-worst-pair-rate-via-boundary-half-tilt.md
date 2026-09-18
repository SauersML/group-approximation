---
rg: 2
id: fpbs-worst-pair-rate-via-boundary-half-tilt
kind: route
title: A boundary with positive Radon-Nikodym growth and finite half-tilted susceptibility above p_c forces the worst-pair rate half the growth
target: fpbs-worst-pair-connectivity-rate-positive-above-pc-universal
requires:
  - fpbs-boundary-half-tilt-above-pc-universal
  - fpbs-boundary-tilted-susceptibility-kernel
artifacts:
  - experiments/boundary-tilt-2026-09-17/check_boundary_tilt.py
---

1. [BT] gives a quasi-invariant `(Z,nu)` with `nu(h_nu >= h) > 0` for some
   `h > 0`, together with `p > p_c` such that `chi^nu_(1/2)(p) < infinity`.
   Countable additivity turns `nu(h_nu > 0) > 0` into the first property.
2. By item 3 of `fpbs-boundary-tilted-susceptibility-kernel`,
   `gamma(p) >= h/2 > 0`. This is (K).
