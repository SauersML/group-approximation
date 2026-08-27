---
rg: 2
id: two-chart-square-lift-no-go-proof
kind: route
title: Compress a child-crossing transport to matrix units
target: two-chart-square-lift-recreates-schur-m2
requires:
  - binary-schur-head-embeddings-are-relative-inner-holonomies
  - branch-flip-pauli-extraction-cancels-schur-surplus
---

# Compress a child-crossing transport to matrix units

Conjugating `p_+` by `t` gives `p_-`, so direct multiplication proves
`(TCL2)`. Two crossing transports have a diagonal return word, giving
`(TCL3)--(TCL4)`, but either one already supplies the matrix units. The
explicit two-dimensional model `(TCL5)` separates consistency of the central
square clause from the Morita-surplus failure. For the Atlas addendum, on the
canonical edge lift every edge message equals the same `U`, so every
alternating rectangle is `I`. Choosing one factor of an edge factorization
instead makes a non-tree edge occur once in its fundamental rectangle, and
its independent right gauge rotates that rectangle while fixing the common
product `U`. Thus neither choice canonically exposes the raw lift.
