---
rg: 2
id: stw08-semiprojective-lfg-khomology-proof
kind: route
title: Lift QD to RFD, then apply Dadarlat's rational K-homology theorem
target: stw08-semiprojective-lfg-khomology-positive-class
requires:
  - semiprojective-mf-algebras-are-rfd
  - dadarlat-rfd-lfg-rational-khomology-uhf-embeds
artifacts:
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

Quasidiagonality implies MF.  Semiprojectivity then lifts the faithful matrix
corona representation to a faithful product representation, so `A` is RFD by
`semiprojective-mf-lifts-to-tail-product-proof`.  The remaining hypotheses
are exactly those of Dadarlat's theorem, which embeds `A` into a UHF algebra.
