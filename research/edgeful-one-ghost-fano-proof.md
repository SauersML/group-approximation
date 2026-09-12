---
rg: 2
id: edgeful-one-ghost-fano-proof
kind: route
title: Check Schaefer witnesses, translate the deleted hyperplane, and list two cube edges
target: edgeful-one-ghost-fano-relation
requires:
  - quantum-polymorphism-commutativity-gadget
---

The seven tuples in `(EOF2)` are obtained by taking `(x_1,x_2)` equal to
`10` or `01` and deleting `1000`.  The four displayed operations are direct
coordinate calculations, so Schaefer's dichotomy gives NP-completeness.

The three points `1001,1010,1011` have XOR `g`, placing the ghost in the
affine hull.  Since the relation is contained in the three-dimensional
affine hyperplane `H_edge`, its affine hull is exactly `H_edge`.  Translation
by `g` gives the seven nonzero points of the three-dimensional vector space
`V`.  The usual Fano argument says that zero enters the affine hull of a
subset of `V\{0}` exactly when the subset contains a three-point line; this
proves `(EOF4)`.

Finally the two pairs in `(EOF5)` belong to `(EOF2)` and have the stated
coordinate differences.  The first serves prescribed coordinates `1,2,3`,
and the second serves coordinate `4`.

For `(EOF6)`, the parity equation is automatic from `x_1=1-x_2`.  If
`(u,v)=(0,0)`, the chosen fourth bit prevents the ghost; otherwise at least
one of `x_2,x_3` already differs from the ghost.  Hence every visible pair
extends.  Variables in one BCS context commute in every operator model, so
the same row is an exact commutativity gadget.
