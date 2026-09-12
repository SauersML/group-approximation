---
rg: 2
id: leavitt-df-failure-from-kernel-local-pair
kind: route
title: A strict one-sided inverse pair over the identity refutes direct finiteness
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - leavitt-kernel-unitization-not-directly-finite
artifacts:
  - research/artifacts/leavitt-kaplansky-pair-dichotomy-2026-09-12.md
---

The prerequisite supplies `alpha = 1 + k` and `beta = 1 + l` in `F_2[R^x]` with
`beta alpha = 1 != alpha beta`. That is exactly the headline's pair. Nothing else is used.

Together with `leavitt-direct-finiteness-failure-from-left-invertible-lift`, this route covers
every strict pair: by `leavitt-kaplansky-pairs-split-kernel-local-or-s0-lift`, a strict pair is a
group translate of this prerequisite's form or of that route's.
