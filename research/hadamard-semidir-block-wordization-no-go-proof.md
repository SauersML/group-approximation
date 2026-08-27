---
rg: 2
id: hadamard-semidir-block-wordization-no-go-proof
kind: route
title: Intersect the Hadamard conjugate of the selector centralizer with itself
target: hadamard-does-not-semidir-independent-selector-blocks
requires:
  - hadamard-selector-commutator-charges-two-path-leakage
---

# Intersect the Hadamard conjugate of the selector centralizer with itself

Multiplying the fixed `2 by 2` matrices gives `(HSW2)`.  Its off-diagonal
block vanishes exactly when the two selector blocks agree, proving the
HNN/semidirect no-go.  For a central selector, expand the two compressed
equalities in the group basis.  Equality of the resulting two-element
cosets gives `(HSW6)--(HSW7)`.  These calculations exhaust the natural
normalizer and central-spectral wordization mechanisms.

