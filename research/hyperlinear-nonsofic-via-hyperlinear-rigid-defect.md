---
rg: 2
id: hyperlinear-nonsofic-via-hyperlinear-rigid-defect
kind: route
title: A hyperlinear group with a nontrivial rigid defect is nonsofic
target: hyperlinear-nonsofic-group
requires: [hyperlinear-group-carries-nontrivial-rigid-defect, sofic-groups-kill-rigid-compression-defects]
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

1. Let `H` be hyperlinear with rigid pair `Gamma <= G <= H` and
   `[g z g^-1, gamma] != 1`, where `z in C_H(Gamma)`.
2. If `H` were sofic, `sofic-groups-kill-rigid-compression-defects` would make
   that commutator trivial.
3. So `H` is hyperlinear and nonsofic.

This is branch (b) of the win--win `hyperlinear-groups-kill-rigid-compression-defects`.
Its premise is supplied by any trace-preserving representation of an
infranormal Kazhdan pair into a tracial matrix ultraproduct that fails to
normalize the relative commutant; see
`rigid-compression-defect-normalization-dichotomy`.
