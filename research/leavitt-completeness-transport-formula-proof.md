---
rg: 2
id: leavitt-completeness-transport-formula-proof
kind: route
title: Additivity of the root map on the two halves of 1, and the characteristic-two commutator expansion
target: leavitt-completeness-transport-formula-for-root-data
requires: []
artifacts:
  - research/artifacts/rank-four-completeness-check-2026-09-12.md
---

Section 2 of the artifact, Proposition 3.

1. **(a)** `e_0 + e_1 = 1` in `R` and the root subgroup `x_ac(R)` is additive, so
   `x_ac(1) = x_ac(e_0) x_ac(e_1)` and the two factors commute. Expanding
   `1 + N = (1 + E_0)(1 + E_1)` gives the circle sum. In characteristic two `x_ab(r)^2 = x_ab(2r) = 1`,
   so `n_ab(r)^2 = sigma(x_ab(r))^2 - 1 = 0`.
2. **(b)** The Steinberg relation `[x_ab(s_i), x_bc(t_i)] = x_ac(s_i t_i)` holds in `EL_n(R)`,
   `n >= 3`. Write `X = 1 + A`, `Y = 1 + B`, with `X^(-1) = X`, `Y^(-1) = Y` and `A^2 = B^2 = 0`.
   Then `XY = 1 + A + B + AB`, and squaring modulo two gives
   `XYXY - 1 = AB + BA + ABA + BAB + ABAB`.
3. **(c)** Sum (b) over `i` and substitute `E_0 + E_1 = N + E_0 E_1` from (a).
4. **Natural models.** For `n_ab(r) = rho(r) E_ab`, every reversed product contains `E_bc E_ab = 0`
   or `E_ac E_ab = 0`, and `E_0 E_1` contains `E_ac E_ac = 0`.
