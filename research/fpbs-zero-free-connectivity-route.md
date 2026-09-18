---
rg: 2
id: fpbs-zero-free-connectivity-route
kind: route
title: Continue the flat walk rate around p_c through a complex zero-free region
target: fpbs-benjamini-schramm-universal
requires:
  - fpbs-zero-free-connectivity-gives-flat-rate
  - fpbs-connectivity-polynomials-zero-free-around-criticality
artifacts:
  - research/artifacts/fpbs-zero-free-connectivity-2026-09-17.md
---

The universal hypothesis gives (ZG) on every nonamenable Cayley graph.
Theorem (b) of `fpbs-zero-free-connectivity-gives-flat-rate` then gives
`p_c<p_u`. The route never needs a real-variable estimate at `p_c` itself, and
it is separate from the pivotal-budget route: the budget gives only a Lipschitz
rate, while (ZG) gives a flat one. The gate is the growth step (G), uniformly
in `R`.
