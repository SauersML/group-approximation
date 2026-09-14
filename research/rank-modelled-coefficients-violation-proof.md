---
rg: 2
id: rank-modelled-coefficients-violation-proof
kind: route
title: Tensor-square the natural model through the rank model of the coefficients
target: rank-modelled-coefficients-violate-two-root-identities
requires: []
artifacts:
  - research/artifacts/el3-two-root-self-similarity-2026-09-12.md
---

Artifact Section 4, Theorem 3.

- **Natural model.** `GL_3(phi)` maps `EL_3(T)` into `GL_3(M_omega)`, and `M_3(M_omega)` is a
  rank ultraproduct.
- **Tensor square.** Take levelwise representatives and square them. The result is well defined
  modulo rank-null sequences, because
  `rk(A (x) A - A' (x) A') <= 2 rk(A - A')` after normalization, and it is multiplicative.
- **The product.** Unitality puts `x_ab(1)` at `(1 + E_ab)^((x)2)`. Since `E_23 E_12 = 0`, the
  product `N_23 N_12` is `E_23 (x) E_12 + E_12 (x) E_23`, of normalized rank `2/9`.
