---
rg: 2
id: leavitt-area-ten-partition-proof
kind: route
title: Exclude the two simple bipartite cores and restore one edge in every area-eight bipartite core
target: leavitt-area-ten-short-atlas-partitions
requires:
  - leavitt-even-region-short-atlas-has-area-ten
---

If there is no digon (and no monogon, since every face is even and nonempty),
the cubic map is a simple bipartite graph with color classes of size five.
Its `5 x 5` adjacency matrix has row and column sum three; the complementary
matrix has row and column sum two.  Hence, up to row/column permutations,
the complement is either one 10-cycle or a disjoint 4-cycle and 6-cycle.
The two resulting cubic bipartite graphs are nonplanar (the elementary
Kuratowski contraction in each case is a `K_(3,3)`).  Therefore a planar
core has a parallel pair, and in a cubic rotation two parallel edges bound
a digon.  Hence a digon exists.

Contract it.  The resulting eight-vertex map is cubic, planar, bipartite,
and has one of the five adjacency-core types and six rotation partitions
classified in `leavitt-eight-cell-curvature-proof`.  For each of the 33
rotation systems, restore each of its twelve edges by a two-vertex digon
gadget.  The 396 restorations yield precisely `(ATP1)`.
