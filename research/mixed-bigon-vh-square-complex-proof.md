---
rg: 2
id: mixed-bigon-vh-square-complex-proof
kind: route
title: Eliminate decoder letters along the tree and read parallel edges as squares
target: mixed-bigon-difference-graphs-present-vh-square-complexes
requires:
  - table-groups-are-memory-holonomy-groups
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
---

Section 2 of the artifact, Theorem B.

Theorem H presents `U_E` on the memory letters, with one relator
`w_s = w_s' delta_e` per non-tree edge. For an edge parallel to the tree edge `t`, the
tree identity `w_s = w_s' delta_t` turns the relator into `delta_t delta_e^(-1) = 1`,
or `delta_t delta_e = 1` for a reversed edge. With mixed types this word is
`h v^(-1) h' v'^(-1)`, an alternating square.

For the converse, the star partition's difference graph is a star with double edges.
The first edge of each pair is the tree edge, so the relators are exactly the squares.
