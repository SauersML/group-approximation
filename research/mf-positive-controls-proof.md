---
rg: 2
id: mf-positive-controls-proof
kind: route
title: Restrict corona models and use regular representations of finite stages
target: mf-positive-controls
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/OperatorMFPositiveControls.lean
  - GroupApproximation/Sofic/LocallyFiniteMF.lean
---

## Direct proof

Restriction preserves a faithful corona representation.  For a residually
finite group, take left-regular permutation representations of a descending
separating sequence of finite quotients.  For a locally finite group, use an
increasing chain of finite subgroups and their regular representations,
extended by the identity off each stage.  Multiplication is eventually exact,
and every nonidentity element eventually acts without fixed points, giving a
uniform positive operator-norm separation from the identity.
