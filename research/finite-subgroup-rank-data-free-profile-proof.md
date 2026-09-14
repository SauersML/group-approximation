---
rg: 2
id: finite-subgroup-rank-data-free-profile-proof
kind: route
title: Free modules restrict to free modules and are isomorphism invariant, and (b-1)(a-1) has rank 3 on the regular module of D_8
target: finite-subgroup-rank-data-cannot-force-two-root-identity
requires: []
artifacts:
  - research/artifacts/el3-two-root-identities-2026-09-12.md
---

Complete proof: artifact Section 6.3.

- **Restriction.** `F_2[L] ~= F_2[K]^([L:K])` as left `F_2[K]`-modules, so
  `rank lambda_L(alpha) = [L:K] rank lambda_K(alpha)`, and the normalized ranks agree.
- **Conjugation.** Every isomorphism of finite groups induces an isomorphism of their regular
  modules.
- **The value.** Put `x = g - 1` and `y = h - 1`. Then
  `F_2[D_8] = F_2<x, y> / (x^2, y^2, xyxy - yxyx)`, with basis
  `1, x, y, xy, yx, xyx, yxy, xyxy`.
  - Left multiplication by `yx` sends `1, y, yx` to `yx, yxy, yxyx` and kills the other five
    basis elements. So its rank is `3`, and `r_D = 3/8`.
  - `g = x_12(1)` and `h = x_23(1)` generate `UT_3(F_2) ~= D_8`, since
    `x_12(1) x_23(1) = 1 + E_12 + E_23 + E_13` has order `4`.
