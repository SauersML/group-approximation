---
rg: 2
id: mf-horn-obstruction-from-literal-mark
kind: route
title: Transport the literal mark through tuples in MF groups
target: mf-universal-horn-obstruction
requires: [literal-central-mark-corona-invisible]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralUniversalHorn.lean
---

## Why sufficient

A tuple satisfying the literal relators induces a homomorphism from `E`.
Composing a map into an MF group with a faithful corona embedding makes the
image of `w` trivial by `literal-central-mark-corona-invisible`.  The
canonical tuple supplies the counterexample outside the MF class because its
mark is nontrivial.
