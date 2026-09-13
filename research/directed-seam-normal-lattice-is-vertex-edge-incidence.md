---
rg: 2
id: directed-seam-normal-lattice-is-vertex-edge-incidence
kind: claim
title: Three-torsion-generated Kazhdan seam groups realize the down-set lattice of vertex-edge incidence as their full normal lattice
distinct_from:
  three-torsion-kazhdan-seam-is-just-non-mf: that has one edge and five normal subgroups; this classifies all normal subgroups for any finite directed graph and shows their lattice is independent of edge orientation.
artifacts:
  - research/artifacts/pestov91-directed-seams-and-normal-lattices-2026-09-13.md
---

For a finite graph `D`, the constant-length binary coding in section 3
gives `G_D=EL_(3ell)(R_D)` with three torsion generators of orders
`7,2,2`, property (T), and no nontrivial finite quotients. Its endpoint
quotient is a product of infinite simple Kazhdan LEF groups and its
kernel is one infinite simple locally finite factor per edge.

Its normal subgroups are exactly the pairs `(J,S)`, with `J subset E`
and `S subset V`, such that every edge incident to `S` is in `J`.
Inclusion is componentwise, so the normal lattice is the distributive
down-set lattice of incidence, with each edge below its endpoints.
The group is centerless and its direct-product decomposition is
exactly the decomposition of the underlying graph into connected
components.
