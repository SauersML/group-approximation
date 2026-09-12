---
rg: 2
id: nonhyperlinear-via-schur-amplified-parity-compressor
kind: route
title: Promote the positive-density parity compressor through an explicit Higman embedding
target: non-hyperlinear-group
requires:
  - schur-amplified-parity-compressor-hs-return
  - mikaelian-explicit-higman-embedding
---

The augmented compressor is finitely generated and recursively presented,
its central word `J` is nontrivial, and every homomorphism into a tracial
matrix ultraproduct kills `J`.  Its canonical group trace therefore cannot
embed in such an ultraproduct, so the augmented group is nonhyperlinear.

Apply the explicit Higman algorithm and retain the embedded word representing
`J`.  Hyperlinearity passes to subgroups, so the finitely presented overgroup
is also nonhyperlinear.
