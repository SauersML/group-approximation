---
rg: 2
id: nonaugmentation-rank-function-from-f2-linear-soficity
kind: route
title: Pull the rank back from a linear sofic embedding of the Leavitt unit group
target: binary-leavitt-units-carry-nonaugmentation-rank-function
requires:
  - binary-leavitt-unit-group-is-f2-linear-sofic
artifacts:
  - research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md
---

Artifact Section 2.4.
- A linear sofic approximation over `F_2` gives a homomorphism of `R^x` into the units of a rank
  ultraproduct `prod_ω M_(n_i)(F_2)/ker`. Every nontrivial element lies at rank distance at least `κ > 0`
  from `1`.
- Its linear extension is a ring homomorphism from `F_2[R^x]`. The ultraproduct rank pulls back to a
  Sylvester matrix rank function with `rk(1 - [x]) >= κ` for `x != 1`, which is not the augmentation rank.
