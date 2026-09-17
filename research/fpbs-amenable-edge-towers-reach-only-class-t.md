---
rg: 2
id: fpbs-amenable-edge-towers-reach-only-class-t
kind: claim
title: Amenable-edge towers from a finitely generated group reach only groups exhausted by iterated amenable normal closures
distinct_from:
  fpbs-fixed-price-amenably-generated-from-fg: that proves fixed price on AG by one amalgam step; this bounds what any finite tower of amenable-edge graphs of groups can reach, at every height, and names a class (groups onto infinite free products) that no height reaches.
  fa-subgroups-of-graph-towers-lie-in-base-pieces: that locates FA subgroups inside base groups of a tower; this is a quotient invariant of the base group of a tower whose top is finitely generated.
artifacts:
  - research/artifacts/fpbs-amenable-edge-tower-reach-2026-09-17.md
---

**Definitions.**
- `T_0 = {1}`.
- `T_r` is the class of groups `Q` having an amenable subgroup `M` with
  `Q/<<M>> in T_{r-1}`.
- `T` is the union of the `T_r`.

An *amenable-edge tower* over `Gamma` is a finite sequence `Gamma = K_0 <= K_1 <= ... <= K_n`.
Each `K_j` is the fundamental group of a finite graph of groups with amenable
edge groups, with `K_{j-1}` as one vertex group. The tower *reaches*
`Gamma` if `K_n` is finitely generated.

**Statement.**
1. If some amenable-edge tower reaches `Gamma`, then `Gamma in T`.
2. `T` is closed under quotients, and a free product of infinitely many
   nontrivial groups is not in `T`. Hence no amenable-edge tower of any height
   reaches a countable group that surjects onto such a free product. Examples:
   `F_inf`, and every extension `N -> Gamma ->> F_inf`.

**Consequence for the fixed-price passage.**
- Any amalgam/HNN descent of fixed price along a tower of the Theorem 1 kind
  (`research/artifacts/fpbs-amalgam-descent-amenably-generated-2026-09-16.md`)
  cannot reach groups outside `T`, whatever descent step is used.
- The step where every such attempt dies is the bottom of the quotient chain.
  It never becomes trivial, because infinitely many free factors survive.
- `T` strictly contains `AG`. For example, `Gamma_mal in T_2`. So Theorem 1
  plus this claim do not rule out reaching into the open class. Artifact §3
  shows that height `<= 2` towers do not reach `Gamma_mal`.
