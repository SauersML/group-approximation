---
rg: 2
id: fixed-rational-packet-hall-no-go-proof
kind: route
title: Clear denominators in the packet restriction and Hall polytope
target: fixed-packet-hall-atlas-has-no-julia-cutoff-gap
requires:
  - finite-graph-of-groups-representation-types-are-integer-flows
  - atlas-a4-context-types-live-in-fixed-rational-polytope
  - index-density-is-amplification-stable
---

The integer-flow theorem writes every fixed packet diagram as a finite
nonnegative integral kernel of restriction matrices.  Divide by total
dimension to obtain `(RPH2)`.  Rationality of all matrices makes rational
points dense in every face, and clearing denominators realizes those points
by matrix multiplicities.

For a finite capacitated bipartite graph, Hall's theorem is the finite family
of inequalities comparing the capacity of each left subset to that of its
neighbor set.  These capacities are rational linear functions of `x`.
Continuity therefore extends every matrix-valid Hall inequality to the whole
real polytope, proving the claim.
