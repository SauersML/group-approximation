---
rg: 2
id: kazhdan-clifford-construction-proof
kind: route
title: Build the Clifford sign and apply the central-sign criterion
target: kazhdan-clifford-non-mf-construction
requires: [central-sign-corona-obstruction]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/KazhdanCliffordConstruction.lean
---

## Why sufficient

The ascending HNN extension acts on the cosets of the level-zero Kazhdan
group.  The element outside the self-embedding image separates two cosets;
the corresponding Clifford generators anticommute, so the marked defect
square is the nontrivial central sign.  The presentation uses only finitely
many compression, centralizer, and centrality relators.  The
`central-sign-corona-obstruction` then kills the sign in every corona model,
while the Clifford quotient proves it nontrivial and preserves the base.
