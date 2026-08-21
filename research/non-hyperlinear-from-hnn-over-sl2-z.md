---
rg: 2
id: non-hyperlinear-from-hnn-over-sl2-z
kind: route
title: Centralize SL2(Z) inside a flexibly stable SL2(Z[1/2]) by a new letter
target: non-hyperlinear-group
requires:
  - iwahori-local-global-defect-question
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
  - hnn-over-codense-kazhdan-subgroup-not-hyperlinear
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
---

`iwahori-local-global-defect-question` is the flexible HS-stability of
`SL_2(Z[1/2])`.  With the co-dense `(tau)` pair
`SL_2(Z) <= SL_2(Z[1/2])`, `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`
makes `<SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1>` a finitely presented
nonhyperlinear group.  Same open input as `iwahori-sector-closure`,
different and simpler witness: an HNN extension in place of a finite
central extension, proved by a direct microstate argument rather than
through asymptotically projective representations.
