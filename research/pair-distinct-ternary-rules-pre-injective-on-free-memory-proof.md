---
rg: 2
id: pair-distinct-ternary-rules-pre-injective-on-free-memory-proof
kind: route
title: Distinct identified pairs force each changed site into two shared triangles, impossible in the claw forest of a free group
target: pair-distinct-ternary-rules-pre-injective-on-free-memory
requires: []
artifacts:
  - research/artifacts/unbalanced-design-memory-collisions-2026-09-12.md
---

Artifact, Section 3, Proposition 10.

- **Hiding a change needs a matching pair.** Let `x` and `x'` differ exactly on a finite nonempty `F`,
  with equal images. Consider a block that reads exactly one changed site `g`, at address `m`. It keeps
  its output only if its context is insensitive and `{x(g), x'(g)} = P_m`. The three pairs are distinct,
  so this happens at most once among the three blocks reading `g`.
- **Each changed site is shared twice.** So every `g` in `F` lies in at least two triangles
  `{h, ha, hb}` that meet `F` again.
- **The incidence graph is a forest.** In the Cayley tree of `F(a, b)`, the claws `h — ha`, `h — hb`
  are edge-disjoint and cover the tree. A cycle in the site–triangle incidence graph would give a
  closed reduced walk in the tree: it would be geodesic inside each claw, and no backtrack is possible
  at a junction.
- **Counting.** On `F ⊔ T_F`, where `T_F` is the set of triangles meeting `F` at least twice, the
  forest has at most `|F| + |T_F| - 1` edges but at least `max(2|F|, 2|T_F|)` edges.
