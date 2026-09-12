---
rg: 2
id: reversed-root-pair-forces-root-squares-proof
kind: route
title: Weyl conjugation spreads the reversed pair identity and the commutator formula kills every root square
target: reversed-root-pair-identity-forces-root-squares-to-vanish
artifacts:
  - research/artifacts/rank-four-plan-adversarial-audit-2026-09-12.md
---

Proof, artifact Section 5. No characteristic is used.

1. **Weyl spread.** Conjugation by the signed permutation matrices of `EL_3(Z)` sends `x_ab(1)` to
   `x_(pi(a) pi(b))(+-1)`. We have `N_x(-1) = -U_x N_x = -N_x U_x` with `U_x = (1+N_x)^-1`. So a
   signed product `N_x(+-1) N_y(+-1)` is `U_x^(0 or 1) (N_x N_y) U_y^(0 or 1)` up to sign, and it
   vanishes iff `N_x N_y` does. `S_3` acts regularly on ordered triples of distinct indices. So
   `N_23 N_12 = 0` gives `N_jk N_ij = 0` for all distinct `i, j, k`.
2. **Commutator formula.** Fix distinct `i, j, k`, and put `X = 1 + N_ij`, `Y = 1 + N_jk`. From
   `x_ik(1) = [x_ij(1), x_jk(1)] = X Y X^-1 Y^-1`,
   `N_ik = (XY - YX) X^-1 Y^-1 = N_ij N_jk X^-1 Y^-1`, since `XY - YX = N_ij N_jk - N_jk N_ij`.
3. **Absorption.** `Y^-1 - 1 = -Y^-1 N_jk`, so `Y^-1 N_ij = N_ij - Y^-1 N_jk N_ij = N_ij`. Also
   `X^-1` commutes with `N_ij`. Hence `N_jk X^-1 Y^-1 N_ij = N_jk N_ij X^-1 = 0`.
4. **Squares.** `N_ik^2 = N_ij (N_jk X^-1 Y^-1 N_ij) N_jk X^-1 Y^-1 = 0`. Every root `ik` of `EL_3`
   has a middle index `j`, so every square vanishes. QED
