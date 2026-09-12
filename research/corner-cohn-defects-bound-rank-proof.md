---
rg: 2
id: corner-cohn-defects-bound-rank-proof
kind: route
title: Rank of a two-by-two product that factors through a row supported in x
target: corner-cohn-defects-bound-rank-in-rank-ultraproducts
requires: []
artifacts:
  - research/artifacts/rank-four-completeness-check-2026-09-12.md
---

Section 1 of the artifact, Theorem 1.

1. Write `S_j = x y_j`. Form the row `S = [S_0  S_1] = x [y_0  y_1]` and the column
   `T = [T_0 ; T_1]`. Rank is submultiplicative, so `rk(TS) <= rk(S) <= rk(x)`.
2. `diag(x, x) = TS + Delta`, where `Delta_ij = delta_ij x - T_i S_j`.
3. Combine these with `rk(diag(x, x)) = 2 rk(x)`, subadditivity of rank, and the fact that a block
   matrix has rank at most the sum of its blocks' ranks:
   `2 rk(x) <= rk(TS) + rk(Delta) <= rk(x) + sum rk(Delta_ij)`.

Each of these rank facts holds for rectangular matrices over a field, and each passes to the
ultralimit. The ultraproduct rank of a rectangular matrix is well defined, because a null
perturbation changes the rank by a null amount. For the dual version use `rk(TS) <= rk(T) <= rk(x)`.
The corollary uses faithfulness: `rk(x) = 0` implies `x = 0` in `M`.
