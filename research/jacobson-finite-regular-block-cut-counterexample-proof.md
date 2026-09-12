---
rg: 2
id: jacobson-finite-regular-block-cut-counterexample-proof
kind: route
title: Compare shifted finite-subgroup averages in a regular representation on a long block cycle
target: jacobson-full-packet-spectral-cuts-do-not-preserve-norm
requires: []
artifacts:
  - research/artifacts/jacobson-full-packet-spectral-cuts-do-not-preserve-norm-2026-09-08.md
---

In a finite ambient binary linear group, take the nested full linear
groups on centered blocks, and average their augmentation projections.
The cyclic shift moves each support between its two neighboring stages,
which bounds the commutator of the average by `1/N`. The entire
diagonal `GL_3` normalizes every stage.

Each spectral cut is a single augmentation projection. Testing the
difference of the shifted fixed-space projections on the normalized
indicator of the original subgroup gives a norm lower bound from the
index of their intersection. The same regular representation gives
exact ranks and proves that the commutator rank can tend to zero
relative to the marked support while its norm stays bounded below.
