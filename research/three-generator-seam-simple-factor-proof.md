---
rg: 2
id: three-generator-seam-simple-factor-proof
kind: route
title: Double the endpoints and recognizably interleave the seam bits to obtain a binary rank-three marking
target: three-torsion-kazhdan-group-has-prescribed-simple-mf-factors
requires:
  - binary-letter-repetition-realizes-matrix-amplification
  - heteroclinic-subshift-has-prescribed-mf-quotient
  - unit-idempotent-elementary-group-has-three-torsion-generators
  - elementary-groups-over-fg-rings-have-property-t
  - simple-kazhdan-lef-hosts-all-countable-locally-finite
artifacts:
  - research/artifacts/pestov91-heteroclinic-prescribed-mf-quotients-2026-09-13.md
---

Apply the seam construction at rank six. Letter doubling identifies
each endpoint rank-six group with the rank-three group of an infinite
minimal binary subshift, giving simplicity and the stated marking.

For the ambient group, interleave each payload bit with its phase bit.
The phase sequence is nondecreasing and every payload sequence is not,
so the two possible parities are disjoint compact sets and are clopen
in the resulting binary subshift. The two-phase corner identifies its
ring with `M_2(R)` and its rank-three group with `EL_6(R)`. The binary
unit-idempotent triple therefore gives the three explicit generators
in section 5, of orders `7,2,2`. Property (T) follows from
finite ring generation. The seam theorem gives the exact radical and
the full finite residual. Each endpoint rank-six group contains its
rank-three subgroup, so a universal-odometer input preserves locally
finite universality in that factor.
