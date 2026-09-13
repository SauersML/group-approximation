---
rg: 2
id: greedy-clopen-return-corner-proof
kind: route
title: Greedily separate clopen markers, code return words and write both tower corner maps explicitly
target: clopen-return-towers-transfer-direct-finiteness-and-matrix-rank
requires:
  - subshift-ring-lef-iff-word-edges-lie-on-cycles
artifacts:
  - research/artifacts/pestov91-return-towers-lower-mf-rank-2026-09-13.md
---

Sections 1--2 give the finite greedy marker construction, whose
separation and covering properties bound return times between `k`
and `2k-1`. Return-word coding makes the induced homeomorphism a
finite-alphabet subshift, and its return unit identifies the ring
with `P`. The tower elements `a_i,b_i` give the full corner map
`r -> (b_i r a_j)` and the first-`k`-levels map `A -> sum a_i A_ij b_j`.
Direct finiteness of `P` would imply stable finiteness by the
prerequisite and then direct finiteness of `R_X`.
