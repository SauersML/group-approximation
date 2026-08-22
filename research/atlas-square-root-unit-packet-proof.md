---
rg: 2
id: atlas-square-root-unit-packet-proof
kind: route
title: Freeze the disjoint-plane H18 edge inside the q14 triangular centralizer
target: atlas-square-root-frame-has-unit-packet-residual
requires:
  - atlas-a4-packet-biclique-decomposition
  - atlas-q14-exact-allows-full-coefficient-cyclicity
  - atlas-two-matrix-bezout-rank-gap-criterion
---

In the q14-adapted basis, one `K_(2,4)` packet involution is `I+E14` and
its chosen order-three neighbour acts on the disjoint plane, so their cube
is the involution.  All three triangular frame directions `E13,E14,E24`
commute with that involution.  Therefore either packet orientation evaluates
to the same fixed transvection, of amplified rank `s`.  Its nonzero scalar
entry is the unit polynomial in the two-matrix residual ideal.
