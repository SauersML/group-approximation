---
rg: 2
id: stationary-type-mass-reused-on-infinite-amalgams-proof
kind: route
title: Align edge restrictions recursively on one fixed Hilbert space
target: stationary-type-mass-reused-on-infinite-amalgams
requires:
  - symmetrized-reset-collapses-schur-flow-to-one-ray
---

Root the tree. Keep the prescribed representation at the root. When an edge
joins an already placed parent `v` to a new child `w`, compatibility gives a
unitary `U_w` intertwining the two edge-group restrictions. Conjugate
`rho_w` by `U_w` and use the universal property of the amalgamated free
product. Because a tree has no cycle, this choice creates no further
compatibility condition.

Iterating over finite rooted subtrees gives compatible representations of
their fundamental groups on the same `C^d`. Their union defines a
representation of the countable tree-of-groups fundamental group. At no point
are the vertex spaces direct-summed, so infinitely many vertices cost no
additional dimension and impose no `ell^2` condition.

For the Schur application, `(SRC6)` gives an integral compatible ray for every
full reset. Choose one positive scalar on that ray and a common multiple of
the finitely many simple dimensions. Repeating the same type at every vertex
satisfies every wire restriction equation, so the preceding construction
gives the stationary exact model. Transverse character mixing leaves this
ray fixed and therefore cannot force leakage from it.
