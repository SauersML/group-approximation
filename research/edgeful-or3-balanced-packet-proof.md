---
rg: 2
id: edgeful-or3-balanced-packet-proof
kind: route
title: Count a symmetric ten-point OR distribution and choose three disjoint cube edges
target: edgeful-or3-balanced-private-plane-packet
requires:
  - edgeful-one-ghost-fano-relation
  - edgeful-one-ghost-escape-avoids-term-recurrence
  - one-binary-marginal-block-escape
---

The multiplicities in `(OBP2)` sum to ten.  For coordinate `a`, the positive
assignments are `100,110,101,111`, of total multiplicity `2+1+1+1=5`;
symmetry gives the same count for `b,c`.  The three edges in `(OBP3)` use
six different coordinate copies and differ in exactly the displayed logical
coordinate.  Four coordinate copies remain unused by the rotations.

The coefficient formula `(EHE1)` shows that each plane contributes
off-diagonal terms only to its changed logical coordinate (and, for the
`a`-plane, to the private complement).  Formula `(OBP4)` is conjugation of a
PVM by two corner unitaries, which proves projection, adjoint, orthogonality,
and sum identities without added group equations.
