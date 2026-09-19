---
rg: 2
id: scaling-family-from-kazhdan-clifford
kind: route
title: Vary the affine dilation in the Kazhdan--Clifford construction
target: scaling-family-non-mf
requires: [kazhdan-clifford-non-mf-construction]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/ScalingFamilyEndpoint.lean
---

## Why sufficient

For every `m >= 2`, `diag(m,m,m,1)` scales the translation subgroup by `m`
and fixes the linear generators.  Translation by `e_1/m` is not integral,
so the chosen element remains outside the self-embedding image and the two
Clifford sites remain distinct.  The Kazhdan base and sign argument are
independent of `m`; the closed endpoint verifies the whole quantified family.
