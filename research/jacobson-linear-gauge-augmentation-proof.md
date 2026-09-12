---
rg: 2
id: jacobson-linear-gauge-augmentation-proof
kind: route
title: Compare the first-braid blocks and apply augmentation to the TS off-diagonal equation
target: jacobson-linear-head-gauge-and-ts-augmentation
requires: []
artifacts:
  - research/artifacts/jacobson-natural-head-linear-gauge-and-augmentation-2026-09-08.md
---

The artifact supplies a self-contained characteristic-two linear proof.
Products of the explicit head root differences give coordinate projections,
so the tail preserves the three head-coordinate blocks, while the overlap
commutant preserves the first and third blocks and their complementary sum.
Comparing `HBH=BHB` forces the second diagonal block of `H` to vanish.
The equation `H^2=I` then supplies a split injection of its source into
`Y`; the remaining braid blocks give the stated invariant splitting and
the full normal form.

For the second assertion the artifact directly multiplies the block
semidirect product, without using another unfinished claim. If the TS
word were identity, its off-diagonal block would satisfy
`u.J-r.J=Z`, where `Z` copies `V_3` to `V_2`. Under the augmentation
hypothesis, composing each term on the left with the target augmentation
gives the same source functional. Their difference is zero, while the
augmentation of `Z` is the nonzero coefficient-sum functional on `V_3`.
This contradiction proves the assertion without either braid, the raw
commutation, a rigidity theorem, or a finite-dimensional assumption.
