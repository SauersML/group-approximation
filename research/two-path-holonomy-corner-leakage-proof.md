---
rg: 2
id: two-path-holonomy-corner-leakage-proof
kind: route
title: Expand the two-path Gram matrix and apply the Julia dilation
target: two-path-holonomy-is-paid-by-corner-leakage
requires:
  - d8-two-path-corner-cell-is-a-gauge-free-swap
  - transverse-d8-two-swap-corner-unitarity-collapses-to-one-path
---

# Expand the two-path Gram matrix and apply the Julia dilation

Write `B=AV` for the relative source holonomy `V=A^*B`.  Expanding the Gram
matrix of `(A+B)/2` gives `(TPH3)`.  Comparing it with the Gram matrix of the
arithmetic compression `pYq` proves `(TPH6)` by one Schatten
`L2 times L2 -> L1` estimate.

Conversely, the standard Julia matrix of this contraction is an exact global
unitary whose selected compression is `(A+B)/2`.  Its complementary defect
operator is the square root of the right side of `(TPH3)`, proving `(TPH9)`
and the universal escape.  The two calculations give both directions of the
claimed corner-invariance interface.
