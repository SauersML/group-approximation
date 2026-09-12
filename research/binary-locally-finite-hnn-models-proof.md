---
rg: 2
id: binary-locally-finite-hnn-models-proof
kind: route
title: Regular tower of the locally finite subgroup, with exact intertwiners from free modules of equal rank
target: binary-locally-finite-hnn-models-violate-two-root-identity
requires: []
artifacts:
  - research/artifacts/defect-piece-covariance-letterwise-firewall-2026-09-12.md
---

Artifact Section 2, Theorem 2.1.

1. **Tower.** `Lambda = union Lambda_j` with `Lambda_j` finite. Left regular representations on
   `F_2[Lambda_j]` give a homomorphism `sigma_reg : Lambda -> M^x` into a rank ultraproduct. Since
   `F_2[Lambda_j]` is free over every finite subgroup `Q`, `rk(sigma_reg(xi)) = rank(lambda_Q(xi)) / |Q|` for
   `xi` in `F_2[Q]`.
2. **Letters.** Exhaust `B_g` by finite `Gamma_i`. At stage `j` take `i(j) -> infinity` with `Gamma_(i(j))`
   and `g Gamma_(i(j)) g^-1` inside `Lambda_j`. `F_2[Lambda_j]` is free of rank `[Lambda_j : Gamma_(i(j))]`
   through both `a -> lambda_j(a)` and `a -> lambda_j(g a g^-1)`, so an exact intertwiner `X_j` exists, and
   `[X_j]` intertwines on all of `B_g`.
3. **Extension.** Independent choices for countably many letters give the model of `H(Lambda, I)`.
4. **Defect.** `<x', y'>` is dihedral of order 8. With `a = 1 + [x']`, `b = 1 + [y']`, the right ideal
   `ba F_2[D_8]` is spanned by `ba, bab, abab`, so the defect has normalized rank `3/8`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 20.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
