---
rg: 2
id: non-linear-sofic-via-f2-rank-row-defect
kind: route
title: If F_2-linear sofic groups kill rigid defects, the Leavitt unit group is not linear sofic over F_2
target: non-linear-sofic-group
requires:
  - f2-linear-sofic-groups-kill-rigid-compression-defects
  - leavitt-unit-group-carries-nontrivial-rigid-defect
---

## Why sufficient

- By [[leavitt-unit-group-carries-nontrivial-rigid-defect]], the Leavitt
  configuration `Gamma = EL_alpha(R) <= G_L = EL_D(R) <= R^x` is a rigid pair.
  It has some `j` in `J = V_(1000)` and `gamma` in `Gamma` with
  `[u j u^-1, gamma] != 1`.
- Suppose `R^x` were `F_2`-linear sofic. Then
  [[f2-linear-sofic-groups-kill-rigid-compression-defects]] with `H = R^x`,
  `g = u` and `z = j` forces that commutator to be `1`.
- So `R^x` is not `F_2`-linear sofic. That is [[non-linear-sofic-group]] with
  `F = F_2`.
- The failure is already visible in the finitely generated packet
  `EL_D(R)`, which equals `R^x`
  ([[leavitt-packet-linear-sofic-kills-kaplansky-target]]).

## Calibration

- This route is independent of the Kaplansky route
  `non-linear-sofic-via-leavitt-kaplansky-failure`: it needs no one-sided
  inverse.
- Its open input is a metric normalization statement, not a certificate.
- Over `F_2` the two routes point the same way. Here, killing the defect
  refutes linear soficity. There, a direct-finiteness witness does.
