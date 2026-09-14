---
rg: 2
id: mixed-bigon-difference-graphs-present-vh-square-complexes
kind: claim
title: Difference graphs made of mixed-type bigons present one-vertex VH square complexes, and every complex with antiparallel squares arises
distinct_from:
  table-groups-are-memory-holonomy-groups: that computes every table group as memory letters modulo cycle holonomies; this identifies the partitions whose holonomies alternate vertical and horizontal letters, so the table group is the fundamental group of a one-vertex VH square complex, and conversely realizes every complex with antiparallel squares by a star partition.
  unicyclic-strict-designs-present-nonsofic-one-relator-groups: that treats difference graphs with one independent cycle; this treats graphs whose cycle space is spanned by parallel edges of opposite type, giving square presentations with many relators.
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
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

**Scope.** A square read `h v^(-1) h' v'^(-1)` in positive letters has antiparallel opposite
sides. A square with one letter on two opposite sides in parallel, such as the
commutator squares of the product complex of `F_V x F_H`, has no such reading under any
orientation of the letters. So a lattice in a product of two trees acting simply
transitively on vertices is the table group of a star partition when its quotient
complex admits an orientation in which every square reads `h v^(-1) h' v'^(-1)`, and not in
general. The first landing of this claim said "in general", which was too strong.

**No strict pair lives on these partitions.** Their memory labels avoid `1_M`, so the
marked class is the origin and every origin cell `(s, 1_M)` is private. By
`private-origin-rows-force-permutation-encoders`, every forward-sufficient rule pair on
them has a symbolwise permutation encoder. A square table that can carry a strict pair
needs decoder addresses that are memory products, glued back to the origin row.
