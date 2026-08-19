---
rg: 2
id: atlas-a4-context-types-live-in-fixed-rational-polytope-proof
kind: route
title: Normalize the graph-of-groups integer-flow cone
target: atlas-a4-context-types-live-in-fixed-rational-polytope
requires:
  - atlas-a4-context-network-simultaneous-hs-exactification
  - finite-graph-of-groups-representation-types-are-integer-flows
---

Apply the established integer-flow classification to the fixed atlas context
graph of groups.  Its vertex and edge groups are fixed finite groups, so the
free abelian modules of irreducible multiplicities and the restriction matrix
`d_G` have fixed finite rank and integer coefficients.

For a representation on a common `d`-dimensional Hilbert space, every vertex
multiplicity vector has dimension-weighted sum `d`.  Divide by `d`.  The
resulting vectors are nonnegative, satisfy the homogeneous rational equations
`d_G x=0`, and satisfy one rational dimension-normalization equation.  Hence
they lie in a fixed compact rational polytope `P_A4`.

Conversely a rational point of `P_A4` can be cleared of denominators to a
positive integer point of `ker d_G`; the integer-flow theorem realizes that
point by a global representation.  Amplifying realizes any further common
denominator.  This proves both assertions.
