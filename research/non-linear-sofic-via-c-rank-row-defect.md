---
rg: 2
id: non-linear-sofic-via-c-rank-row-defect
kind: route
title: If complex-linear sofic groups kill rigid defects, the Leavitt unit group is not linear sofic over C
target: non-linear-sofic-group
requires:
  - c-linear-sofic-groups-kill-rigid-compression-defects
  - leavitt-unit-group-carries-nontrivial-rigid-defect
---

## Why sufficient

- By [[leavitt-unit-group-carries-nontrivial-rigid-defect]], the unit group
  `R^x` of `R = L_(F_2)(1,2)` contains a rigid pair `Gamma <= G_L`, both Kazhdan with
  `Gamma` infranormal, together with `g in G_L`, `z in C_(R^x)(Gamma)` and `gamma in Gamma`
  such that `[g z g^-1, gamma] != 1`.
- Suppose `R^x` were linear sofic over `C`. Then
  [[c-linear-sofic-groups-kill-rigid-compression-defects]] with `H = R^x` forces that
  commutator to be `1`.
- So `R^x` is not linear sofic over `C`. That is [[non-linear-sofic-group]] with `F = C`.

## Calibration

- This route runs parallel to `non-linear-sofic-via-f2-rank-row-defect` over `F_2`.
  Neither prerequisite is known to imply the other. Arzhantseva--Paunescu Question 8.6
  asks whether linear soficity passes to a fixed finite field, and no comparison of the
  two classes is recorded here.
- It needs no ring-level rigidity. It fails with its prerequisite if some `C`-linear
  sofic group carries a rigid defect, and that failure would instead answer
  Arzhantseva--Paunescu Question 8.5 through
  `linear-sofic-nonsofic-via-c-rank-row-defect`.
