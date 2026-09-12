---
rg: 2
id: braid-prefix-label-space-ucp-obstruction-proof
kind: route
title: Use the diagonal multiplicative domain and an exact rank-one negative witness on the braid hexagon
target: braid-prefix-label-space-has-no-ucp-expectation
requires: []
artifacts:
  - research/artifacts/braid-prefix-label-space-ucp-obstruction-2026-08-21.md
---

Every `E_ii` belongs to the repeated-label space.  A ucp projection onto that
space fixes each `E_ii`; Schwarz equality places all of them in its
multiplicative domain, so the projection is a diagonal-bimodule map and acts
entrywise on matrix units.  Since it must fix the equal-labelled sum of three
`x` matrix units, it fixes each summand, contradicting that an individual
summand violates the repeated-label equality.  A fixed-point expectation is
a special case.

For orthogonal averaging, apply the displayed averaging formula to
`v=(-1,0,1,-1,0,1)`.  The averaged Hermitian matrix has quadratic form
`-16/3` at `q=(-1,-1,-1,1,1,1)`, although `vv^*` is positive.

