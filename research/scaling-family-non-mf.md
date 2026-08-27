---
rg: 2
id: scaling-family-non-mf
kind: claim
title: Infinite scaling family of finitely presented non-MF groups
distinct_from:
  torsion-free-finitely-presented-non-mf: Every present scaling example has a nontrivial central involution; the other asks for a torsion-free example.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/ScalingFamilyEndpoint.lean
---

For every integer `m >= 2`, replacing literal doubling by scaling by `m`
produces a finitely presented group `E_m` with a nontrivial central
involution killed by every norm-matrix-corona representation.  Hence every
`E_m`, and both of its group C-star algebras, are non-MF.
