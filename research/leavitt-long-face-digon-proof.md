---
rg: 2
id: leavitt-long-face-digon-proof
kind: route
title: Contract every forced gate digon and compare the resulting face lengths with the complete two- and four-vertex core lists
target: leavitt-long-odd-faces-fail-digon-contraction
requires:
  - leavitt-long-odd-face-core-partitions
---

Distinct digon faces in a connected cubic graph with more than two vertices
are vertex-disjoint.  Indeed a digon consumes two of the three half-edges at
each endpoint.  A second digon through the same endpoint either needs two
more half-edges or makes three parallel edges between the same two vertices;
the latter pair is then a whole connected component.

Contract a digon by deleting its two vertices and joining their remaining
external half-edges.  The digon face disappears and each of its two adjacent
faces loses two corners.  After contracting `m` disjoint digons, distribute
`2m` adjacency incidences among the nondigon faces and subtract twice each
incidence.

For `m=2`, the complete connected planar cubic four-vertex core partitions
are

```text
(1,1,5,5), (1,1,2,8), (1,1,1,9),
(1,2,3,6), (2,2,4,4), (3,3,3,3).                         (DCP1)
```

For `m=3`, the complete two-vertex list is

```text
(1,1,4), (2,2,2).                                        (DCP2)
```

The lists follow directly from the `11!!` and `5!!` ribbon pairings,
respectively, or by classifying loops and parallel edges at cubic vertices.
For `m=4`, the digon gadgets exhaust all eight vertices.  Connectedness
leaves a single vertexless circle after contraction, and restoring the four
gadgets makes both global faces length eight.

For every partition in `(LOP1)`, the artifact enumerates the nonnegative
incidence allocations of total `2m`.  None yields `(DCP1)`, `(DCP2)`, or
the terminal `(8,8)` circle.  Its MSI output is seven empty `MATCHES` lists.
Thus no core exists even before relator colors and orientations are restored.

