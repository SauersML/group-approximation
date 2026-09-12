---
rg: 2
id: non-linear-sofic-via-sylvester-two-root-gate
kind: route
title: If every Sylvester rank function kills the two-root defect, the Leavitt unit group is not F_2-linear sofic
target: non-linear-sofic-group
requires:
  - sylvester-rank-functions-on-leavitt-units-kill-two-root-defect
  - leavitt-rank-functions-killing-two-root-defect-are-augmentation
artifacts:
  - research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md
---

Artifact Corollary 4.
1. Suppose `R^x` is `F_2`-linear sofic, through an embedding `σ` into the units of a rank ultraproduct
   `M` over `F_2` that keeps every nontrivial element at rank distance at least `κ > 0` from `1`.
2. The linear extension `F_2[R^x] -> M` pulls the normalized rank back to a Sylvester matrix rank
   function `rk` with `rk(1 - [x]) >= κ` for `x != 1`, so `rk != rk_ε`.
3. By `leavitt-rank-functions-killing-two-root-defect-are-augmentation`, `rk(D) > 0`. That contradicts
   the first requirement.
4. `R^x` is infinite, so it is a group that is not linear sofic over `F_2`.
