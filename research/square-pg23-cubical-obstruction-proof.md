---
rg: 2
id: square-pg23-cubical-obstruction-proof
kind: route
title: Euclidean recubulation forces a Kazhdan fixed point and contradicts the Euler characteristic
target: square-pg23-groups-cannot-be-kazhdan
requires: []
artifacts:
  - research/artifacts/square-pg23-cubical-obstruction-2026-09-12.md
---

The `PG(2,3)` incidence graph is simple with girth six. Give every square
of `K` the Euclidean unit-square metric. Its links are flag graphs, so the
universal cover is a two-dimensional CAT(0) cube complex. The deck action
is free and cellular. Niblo--Reeves, *Groups acting on CAT(0) cube
complexes* (1997), Theorem B, says that a Kazhdan group acting on such a
complex fixes a point. Hence a Kazhdan deck group would be trivial.

But each link has 26 vertices and 52 edges. Incidence counting gives
`|E| = 13|V|`, `|F| = 13|V|`, and `χ(K) = |V| >= 2`. A trivial deck
group would make `K` itself CAT(0), hence contractible with `χ(K) = 1`.
This contradiction proves the non-Kazhdan assertion.

For the extra spectral assertion, the artifact computes the normalized
adjacency of the subdivided link using its vertex-edge incidence matrix;
the square of each positive eigenvalue is `(1+λ)/2`, where `λ` is a
normalized adjacency eigenvalue of the original link. Its second largest
eigenvalue is `sqrt(3)/4`, yielding the displayed gap.

Primary source checked on 2026-09-12:
[Niblo--Reeves, Theorem B](https://arxiv.org/pdf/math/9702231).
