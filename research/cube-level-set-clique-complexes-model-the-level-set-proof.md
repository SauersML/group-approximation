---
rg: 2
id: cube-level-set-clique-complexes-model-the-level-set-proof
kind: route
title: Slices are spanned by vertices, cubes are Helly, and both complexes share one nerve
target: cube-level-set-clique-complexes-model-the-level-set
requires: []
artifacts:
  - research/artifacts/zp-cube-level-set-rips-2026-09-13.md
---

Full proof in `research/artifacts/zp-cube-level-set-rips-2026-09-13.md`
(Lemmas 1–3 and the proof of Theorem A). Outline:

- **Lemma 1 (slices).** On a cube `[0,1]^k`, `h = c + Σ ε_i x_i` with `c ∈ Z`
  and `ε_i ∈ {−1,0,1}`. A vertex of the slice `C ∩ L` lies on a face of
  dimension `<= 1`, and on an edge with `ε_j ≠ 0` the zero of `h` is at an
  integer parameter. So `C ∩ L = conv(C ∩ V_0)`.
- **Lemma 2 (squares).** If the hyperplanes dual to edges `[a,b]` and `[a,c]`
  cross, the median of `b`, `c` and a vertex in the `(b,c)`-quarter is a fourth
  vertex of a square.
- **Lemma 3 (Helly).** For a finite set `A` of vertices lying pairwise in common
  cubes, every separating hyperplane is dual to an edge at a fixed `a ∈ A`, and
  any two of them cross: two non-crossing ones would both separate some
  `p, q ∈ A`, which lie in a common cube. By Lemma 2 and the flag link condition,
  these edges span a cube at `a`, and that cube contains `A`.
- **Item 1** is Lemma 3.
- **Item 2.** Cover `L` by `C ∩ L` and `K` by the full simplices on `C ∩ V_0`,
  over cubes `C` meeting `V_0`. Intersections of cubes are cubes, so finite
  intersections on both sides are `conv(D ∩ V_0)` and `Δ(D ∩ V_0)` for the
  cube `D`. Both are contractible when nonempty, and each is nonempty exactly
  when `D ∩ V_0 ≠ ∅`. The two covers have the same nerve, and the nerve
  theorem gives `L ≃ nerve ≃ |K|`.
- **Item 3.** `g ↦ g v_0` is an isomorphism `Cay(N,T) → Θ`, because `N`
  preserves cubes. Then apply `group-rips-complexes-are-cayley-graph-flag-complexes`. ∎
