---
rg: 2
id: two-strand-braid-groups-of-k5-and-k33-have-empty-sigma-proof
kind: route
title: "Count cells and vertex links of UD_2 K_5 and UD_2 K_{3,3}, then use surface-group normal subgroups"
target: two-strand-braid-groups-of-k5-and-k33-have-empty-sigma
requires: []
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part1.md
---

**Cells.** The cells of `UD_2Γ` are:

- unordered pairs of distinct vertices;
- (edge, vertex off its closure) pairs;
- unordered pairs of edges with disjoint closures.

For `K_5` the counts are 10, 30, 15, so `e = −5`. For `K_{3,3}` they are 15,
36, 18, so `e = −3`.

**Links.** The link of a vertex `{u,v}` has one vertex per move
`u→w, w ∉ {u,v}` and per move `v→w, w ∉ {u,v}`. Two moves span an edge iff
they move different particles to different targets. For `K_5` this gives a
hexagon. For `K_{3,3}` it gives a hexagon when `u, v` are on the same side,
and `K_{2,2}` when they are on opposite sides. Every link is a circle, so
the complex is a closed surface. An odd Euler characteristic forces
nonorientability.

**Group.** Abrams' condition for `n = 2` holds: cycles have length `≥ 3`.
So `B_2Γ = π_1(UD_2Γ)`.

**Σ.** The kernel of a nonzero character is a nontrivial normal subgroup of
infinite index. In a closed surface group with negative Euler characteristic
such a subgroup is not finitely generated (Griffiths; pass to the orientable
double cover). So `[χ] ∉ Σ¹`, and `Σ^m ⊆ Σ¹` gives all `Σ^m = ∅`.
