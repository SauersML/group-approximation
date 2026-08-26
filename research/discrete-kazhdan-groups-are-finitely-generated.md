---
rg: 2
id: discrete-kazhdan-groups-are-finitely-generated
kind: claim
title: Every discrete Kazhdan group is finitely generated
artifacts:
  - GroupApproximation/Kazhdan/KazhdanFiniteGeneration.lean
---

Every discrete group with property `(T)` admits a finite symmetric generating
set.

This is kernel-checked as
`KazhdanFiniteGeneration.exists_symmetric_generating_finset`; in particular,
the finite-generation hypothesis in residual-finiteness obstructions applies
automatically to every Kazhdan kernel.
