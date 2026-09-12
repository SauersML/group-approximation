---
rg: 2
id: mixed-bigon-difference-graphs-present-vh-square-complexes
kind: claim
title: Difference graphs made of mixed-type bigons present one-vertex VH square complexes, and every such complex arises
distinct_from:
  table-groups-are-memory-holonomy-groups: that computes every table group as memory letters modulo cycle holonomies; this identifies the partitions whose holonomies alternate vertical and horizontal letters, so the table group is the fundamental group of a one-vertex VH square complex, and conversely realizes every such complex by a star partition.
  unicyclic-strict-designs-present-nonsofic-one-relator-groups: that treats difference graphs with one independent cycle; this treats graphs whose cycle space is spanned by parallel edges of opposite type, giving square presentations with many relators.
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
---

**ESTABLISHED** by `mixed-bigon-vh-square-complex-proof`.

Let `E` be a marked partition of `S x M` with connected loop-free difference graph
`Gamma_E`. Suppose three things:
* `M \ {1} = V ⊔ H`, and every edge label `x_m' x_m^(-1)` uses non-identity addresses;
* every edge outside a spanning tree `T` is parallel to a tree edge;
* a parallel edge with the tree edge's orientation has the opposite type (HV versus
  VH), and a reversed one has the same type.

Then `U_E` is the fundamental group of the one-vertex VH complex with edges `V ⊔ H` and
one square `h v^(-1) h' v'^(-1)` per non-tree edge.

Conversely, every finite one-vertex VH complex with squares
`h_q v_q^(-1) h'_q v'_q^(-1)` equals `U_E` for the star partition with
`S = {1} ∪ {s_q}`, `M = {1} ∪ V ∪ H` and identified pairs `(s_q, v_q) ~ (1, h_q)`,
`(s_q, h'_q) ~ (1, v'_q)`.

In particular, lattices in products of two trees that act simply transitively on
vertices are table groups of partitions. Whether such a partition is minimal
forward-sufficient for some rules is left open in
`strict-automaton-on-lattice-in-product-of-trees`.
