---
rg: 2
id: finite-graph-of-groups-representation-types-are-integer-flows-proof
kind: route
title: Import Gerasimova-Shchepin Proposition 1 for graph-of-groups representation cones
target: finite-graph-of-groups-representation-types-are-integer-flows
requires: []
artifacts:
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
---

Gerasimova--Shchepin, *Virtually free groups are p-Schatten stable*,
arXiv:2107.10032, Section 3.2 define the free abelian representation modules
`Theta_G` on irreducible finite-group representations and the edge-restriction
operator `d_G`.  Their Proposition 1 proves both directions:

```text
rho a representation of pi_1(G)  =>  rho# in Theta_V^+ intersect ker d_G,
```

and every element of that positive integer kernel is realized by a global
representation.

The forward implication is restriction compatibility across each edge group.
For the converse, choose vertex representations with the prescribed
multiplicity vectors, glue them inductively along a spanning tree using unitary
intertwiners of the equal edge restrictions, and use stable-letter intertwiners
on non-tree edges.  This is exactly the claimed integer-flow classification.
