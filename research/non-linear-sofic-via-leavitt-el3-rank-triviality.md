---
rg: 2
id: non-linear-sofic-via-leavitt-el3-rank-triviality
kind: route
title: Triviality of rank models of EL_3 over the binary Leavitt algebra makes that group non-linear-sofic over F_2
target: non-linear-sofic-group
requires:
  - leavitt-el3-rank-models-over-finite-fields-are-trivial
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-rank-ring-rigidity-2026-09-12.md
---

## Why sufficient

- Take `K = F_2`, `n = 2` and `R = L_(F_2)(1,2)`. The elements `x_12(a)`, `a` in `R`, are
  pairwise distinct, so `EL_3(R)` is infinite.
- If `EL_3(R)` were `F_2`-linear sofic, it would embed in
  `prod_omega GL_(n_i)(F_2) / d_omega`, the unit group of a rank ultraproduct over `F_2`, with
  `sigma(g) != 1` for every `g != 1`.
- `leavitt-el3-rank-models-over-finite-fields-are-trivial` makes every such homomorphism
  trivial, a contradiction.
- So `EL_3(L_(F_2)(1,2))` is not `F_2`-linear sofic, which is `non-linear-sofic-group` with
  `F = F_2`.

## Calibration

- This route needs neither the class statement
  `el3-rank-models-factor-through-ring-rank-models` nor property (T), and it survives a linear
  sofic `EL_3` over any other simple ring.
- It runs parallel to `non-linear-sofic-via-el3-ring-rank-rigidity`, whose prerequisite is the
  class statement.

*Verified independently by `gk-vf-linear` (2026-09-12): Section 34 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
