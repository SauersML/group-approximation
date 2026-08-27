---
rg: 2
id: finite-face-flatness-holonomy-classification-proof
kind: route
title: Gauge a spanning tree and read the remaining edges as presentation generators
target: finite-face-flatness-stops-at-fundamental-group-holonomy
requires: []
---

Choose a base vertex and a maximal spanning tree `T` in the one-skeleton.
Recursively choose vertex gauges along `T` so that every oriented tree edge
has label `I`.  The remaining oriented edges are the standard free generators
of the fundamental group of the one-skeleton.  In this gauge, the ordered
holonomy around each two-cell is exactly the word attaching that cell.
Hence face-flatness says precisely that the generator assignment factors
through `pi_1(X)`.

The gauge at the base vertex was not fixed.  Changing it conjugates every
remaining edge label simultaneously.  Conversely, simultaneous conjugation
extends to a vertex gauge, and every representation of `pi_1(X)` labels the
non-tree edges and reconstructs a face-flat connection by putting identity
on `T`.  This proves `(FFH1)`.

If a flat connection from a representation `rho` were pure gauge, the
holonomy of every based loop would be the identity, so `rho` would be
trivial.  Thus any nontrivial `rho` is an exact zero-curvature obstruction to
a curvature-to-pure-gauge estimate with modulus vanishing at zero.

Finally fix the tree and a finite presentation read from the cells.  The
maximum normalized-HS face curvature is exactly the maximum relator defect
of the non-tree edge tuple.  Distance from that tuple to a flat connection is
the generator distance to a genuine representation.  Restoring or removing
the finitely many tree edges uses only products of bounded length, so fixed
word telescoping changes these quantities by constants depending only on
`X`, never on `d`.  This identifies quantitative face repair with
normalized-HS stability of the presentation and completes the proof.
