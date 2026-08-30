---
rg: 2
id: stw99-uct-implies-kk-hausdorff
kind: route
title: Under the UCT, alpha is a continuous isomorphism into a Hausdorff group
target: stw99-problem-v-kk-hausdorff-q-stable
requires: [stw99-problem-ii-nuclear-uct]
artifacts:
  - research/artifacts/stw99-uct-cluster-2026-08-30.md
---

If `B` is separably `Q`-stable then `K_*(B)` is uniquely divisible (a
`Q ≅ K_0(Q)`-module structure on K-theory via `B ≅ B ⊗ Q` separably), so
the UCT for `A` makes `α : KK(A, B) → Hom(K_*(A), K_*(B))` an
isomorphism.  `α` is continuous for the KK-topology and the
pointwise-convergence topology, whose target is Hausdorff (K-groups are
discrete), so the closure of `0` in `KK(A, B)` lies in `ker α = 0`, and
`KK(A, B)` is Hausdorff.
