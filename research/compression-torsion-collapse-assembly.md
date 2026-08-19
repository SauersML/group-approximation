---
rg: 2
id: compression-torsion-collapse-assembly
kind: route
title: Assemble lifts, rank cocycle, FH, and scaled transport
target: compression-torsion-collapse
requires:
  - scaled-kazhdan-transport
  - corona-commuting-torsion-lifts
  - kazhdan-coboundary-collapse
artifacts:
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
---

Full proof in notes/COMPRESSION_COLLAPSE_MF_RADICAL.md section 2: exact
lifts give the rank metric; eventual invariance plus the full generating
set normalizes; the cocycle is nonzero by construction and vanishes on the
compressed copy; FH gives an H-fixed coboundary primitive; scaled forward
transport (matricial Mautner at rank scale, on the mass sector) forces the
primitive to be Lambda-fixed, killing the cocycle.
