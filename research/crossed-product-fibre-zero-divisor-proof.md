---
rg: 2
id: crossed-product-fibre-zero-divisor-proof
kind: route
title: Evaluate an annihilator at one odd measure, and spread a fibre kernel vector over a clopen neighbourhood
target: crossed-product-zero-divisors-are-detected-on-fibres
requires:
  - signed-thompson-algebra-is-odd-measure-crossed-product
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Theorem 2.1 of the artifact.
- `rho_mu` is a representation: `rho_mu([g] f [g]^-1) = rho_mu(g.f)`.
- *1 ⇒ 2.* If `x y = 0` with `y = sum_k [k] d_k != 0`, choose `mu` with some `d_k(mu) != 0`. Then
  `xi = rho_mu(y) delta_1` is nonzero and `x_mu xi = rho_mu(x y) delta_1 = 0`.
- *2 ⇒ 1.* If `x_mu xi = 0`, choose a clopen `W ∋ mu` on which the finitely many functions
  `eta -> b_g(k eta)` are constant. Then `y = sum_k xi_k [k] 1_W` is nonzero, and
  `x y = sum_m [m] 1_W (x_mu xi)_m = 0`.
- *2 ⇔ 3.* The set of `mu` with a kernel vector of given support is clopen, and odd Dirac sums are dense.
- *Right zero divisors* follow by applying the anti-automorphism `[g] -> [g^-1]`.
