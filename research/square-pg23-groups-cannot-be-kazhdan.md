---
rg: 2
id: square-pg23-groups-cannot-be-kazhdan
kind: claim
title: Finite square complexes with PG(2,3) links and at least two vertices cannot have Kazhdan fundamental group
distinct_from:
  square-pg23-kazhdan-hyperbolic-complex-exists: that asks for a Kazhdan complex of this shape; this proves that the requested property is impossible, by changing the cell metric to obtain a CAT(0) cube action
  kazhdan-two-complex-b2-is-euler-characteristic-minus-one: that is a conditional Euler characteristic calculation for arbitrary polygonal complexes; this excludes its proposed square-complex Kazhdan instance
artifacts:
  - research/artifacts/square-pg23-cubical-obstruction-2026-09-12.md
---

Let `K` be a finite connected square complex with at least two vertices and
every vertex link isomorphic to the incidence graph of `PG(2,3)`. Then
`π_1(K)` does **not** have property (T).

This remains true if the squares were originally equipped with hyperbolic
metrics of corner angle `π/3`: replacing them by Euclidean unit squares
preserves the fundamental group and gives a locally CAT(0) cube complex.

Moreover, coning each square to its center produces at every original vertex
a subdivided incidence link whose smallest positive normalized Laplacian
eigenvalue is exactly

```text
1 - sqrt((4 + sqrt(3))/8) < 1/2.
```

Thus the original link gap `1 - sqrt(3)/4 > 1/2` cannot be transferred to
the simplicial spectral criterion. This is an application of classical
cubical fixed-point theory, not a new general fixed-point theorem.
