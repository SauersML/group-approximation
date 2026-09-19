---
rg: 2
id: hadamard-selector-leakage-proof
kind: route
title: Hadamard-rotate a selector-central return and read its off-corner block
target: hadamard-selector-commutator-charges-two-path-leakage
requires:
  - two-path-holonomy-is-paid-by-corner-leakage
---

# Hadamard-rotate a selector-central return and read its off-corner block

On the fixed two-dimensional `D_16` type, selector centrality makes the
return word `diag(A,B)`.  Conjugation by the packet Hadamard gives `(HSC5)`.
Its selected compression is the coherent average, while the complementary
block is the difference.  Commuting this rotated word with the selector
therefore has squared normalized-HS defect exactly `||A-B||_2^2`, and the
positive leakage is one quarter of the same quantity.

Finally `d->1` retracts the presentation onto the finite packet, proving
that the selector and every nonzero packet projection survive.  This proves
both the dimension-free payment and exact completeness assertions.
