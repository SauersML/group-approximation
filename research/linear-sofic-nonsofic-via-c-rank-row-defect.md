---
rg: 2
id: linear-sofic-nonsofic-via-c-rank-row-defect
kind: route
title: A complex-linear sofic group with a nontrivial rigid defect is linear sofic and not sofic
target: linear-sofic-nonsofic-group
requires:
  - c-linear-sofic-group-carries-nontrivial-rigid-defect
  - sofic-groups-kill-rigid-compression-defects
---

## Why sufficient

- By [[c-linear-sofic-group-carries-nontrivial-rigid-defect]], some countable group `H`
  that is linear sofic over `C` contains a rigid pair `Gamma <= G <= H` with a
  nontrivial rigid defect.
- If `H` were sofic, [[sofic-groups-kill-rigid-compression-defects]] would make every
  generator `[g z g^-1, gamma]` of that defect trivial.
- So `H` is linear sofic over `C` and not sofic. That is [[linear-sofic-nonsofic-group]],
  a negative answer to Arzhantseva--Paunescu Question 8.5.

## Calibration

The prerequisite is the negation of
`c-linear-sofic-groups-kill-rigid-compression-defects`, and the two carry each other in
`refuted_by`. Exactly one of this route and `non-linear-sofic-via-c-rank-row-defect`
has a true prerequisite. So one of the two roots is settled once the complex-linear
row is decided.
