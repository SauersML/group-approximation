---
rg: 2
id: primitive-word-four-generator-spectral-proof
kind: route
title: Primitive windows generate matrix units and the order-seven generator bounds the negative spectrum
target: primitive-binary-words-give-four-regular-simple-expanders
requires:
  - unit-idempotent-elementary-group-has-three-torsion-generators
  - binary-subshifts-embed-in-three-marked-kazhdan-groups
  - finite-simple-groups-converge-to-simple-kazhdan-group
artifacts:
  - research/artifacts/pestov91-four-regular-expanders-and-limits-2026-09-13.md
---

Section 1 proves the statement for every primitive binary word.
Its distinct cyclic windows separate positions, so shifted letter
diagonals and the permutation generate the full matrix algebra. Apply
the unit-idempotent theorem and elementary flattening to obtain the
finite special linear group, which is simple over `F_2` in these ranks.

The common source `U` maps onto every such finite group. Its Kazhdan
constant gives the upper adjacency bound via the sum of squared
displacements. Since `c^7=1`, `c+c^{-1}>=-2cos(pi/7)I`; the involutions
are each at least `-I`. Their average gives the stated lower bound.
Distinct orders and block entries verify the exact graph degree.
