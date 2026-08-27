---
rg: 2
id: regular-tree-consistency-gap-proof
kind: route
title: Cut a bounded-degree tree at a centroid edge
target: regular-tree-consistency-has-vanishing-spectral-gap
requires: []
---

Choose a centroid vertex `v`: every component of `T\{v}` has at most `N/2`
vertices.  Since `deg(v)<=Delta`, one component `A` has at least
`(N-1)/Delta` vertices.  Its only boundary edge is the edge joining it to
`v`, which proves `(RTC1)`.  The easy direction of Cheeger's inequality gives
`lambda_2<=2 h`, and `(RTC2)` follows (adding self-loops to make the random
walk regular changes only the fixed `Delta` constant).

For the operator witness choose two reflections `P,Q` with
`||P-Q||_2=c>0`, assign `P` to every vertex of `A` and `Q` to every vertex of
the complement.  Equality loss is zero on all but one of the `N-1` edges, so
its edge average is `c^2/(N-1)`, while every cross-cut pair is still distance
`c`.  Both sides have cardinality bounded below by a fixed `Delta`-dependent
fraction of `N` after choosing the component in `(RTC1)`.

