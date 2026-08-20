---
rg: 2
id: clifford-covariance-regular-flow-proof
kind: route
title: Regard every covariance stable letter as a finite graph-of-groups edge
target: clifford-covariance-atlases-have-regular-flow
requires:
  - controlled-pauli-corner-has-clifford-groupification
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
  - finite-packet-cannot-realize-absorbing-contraction
---

Each Pauli completion is a finite semidirect product.  An ordinary amalgam
identifies two injected finite edge groups.  A stable letter implementing a
finite packet automorphism is an HNN edge whose two edge maps are the identity
and that automorphism.  Thus any finite covariance-only construction has a
finite graph-of-finite-groups description.

Choose a common total dimension divisible by all vertex-group orders and put
the corresponding multiple of the left regular representation at each
vertex.  By `finite-packet-graph-atlases-have-a-regular-stationary-flow`, all
edge restrictions agree and glue to an exact finite-dimensional
representation.  Regular restriction contains every marked Clifford
extension and every visible selector character.  Hence the right side of
`(CFR1)` is positive while every covariance mismatch vanishes.

If the proposed atlas is repeated through the absorbing depth, apply
`finite-packet-cannot-realize-absorbing-contraction` to the same exact type
flow.  This rules out the full contraction chain and proves the stated need
for a non-graph two-cell.

