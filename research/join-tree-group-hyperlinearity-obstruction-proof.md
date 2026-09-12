---
rg: 2
id: join-tree-group-hyperlinearity-obstruction-proof
kind: route
title: Pull back the canonical trace from the residually finite acyclic ambient group
target: cycle-closure-cannot-remain-in-the-join-tree-group
requires:
  - join-tree-bcs-has-explicit-signed-hecke-atlas
  - bcs-corner-model-is-a-compatible-projection-atlas
  - nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear
---

Finite groups and finitely generated free groups are residually finite, and a
finite direct product of residually finite groups is residually finite.
Therefore `(CJG1)` is residually finite and hyperlinear.

A completed atlas in `(CJG2)` gives the unital homomorphism of
`bcs-corner-model-is-a-compatible-projection-atlas`.  Equivalently,
`nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear` would force
`Gamma_T` to be nonhyperlinear.  This contradicts the preceding residual
finiteness.  In trace language, the canonical trace of a hyperlinear group is
Connes embeddable, positive corners preserve Connes embeddability after
normalization, and pullback along a unital star homomorphism preserves it.
