---
rg: 2
id: finite-s3-cross-edge-holonomy-countermodel-proof
kind: route
title: Induce the inverse-twisted regular gauge and count the finite type orbit
target: finite-s3-cross-edge-holonomy-cannot-renew-saturated-escape
requires:
  - btb-three-line-tree-retains-multiplicity-return-gauge
  - agent-aggregate-escape-two-intertwiner-clifford-dichotomy
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
---

The first complete irreducible `S_3` reflection sends the selected line to
its companion, and the packet-reducing child hull therefore contains the
whole two-dimensional local outer type.  For the two edge gauges, restrict
to the stabilizer of that active packet type and write its outer multiplier
as `omega`.  By the finite-holonomy hypothesis, the inverse-twisted regular
representation of the finite quotient `H` satisfies every multiplicity
relation.  Tensoring cancels `omega`, and induction over the finite packet
type orbit gives an honest finite-dimensional covariant representation with
equal multiplicity on every orbit summand.

A stabilizer return preserves the actual saturated local carrier and has no
overlap loss.  A type-moving return enters one new equal summand; after a set
`K` of types has been visited, the actual induced carrier has exactly
`|K|/|O|` of the finite orbit capacity.  Positive regular packet
multiplicities and a scalar forbidden assignment keep the active fiber
nonzero.  This proves the full-overlap/prepaid-orbit dichotomy.
