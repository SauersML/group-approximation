---
rg: 2
id: v-times-shift-groupoid-has-no-finite-similarity-types
kind: claim
title: "The groupoid behind the V-times-shift route admits no finite similarity type system, so piece-counting Stein–Farley filtrations cannot be cocompact"
---

Notation of `v-times-shift-alternating-group-restrictions-are-simple`:
`G = G_V × (Z ⋉ Σ)` on `X = C × Σ`. "Similarity type system" is in the sense of
`finite-similarity-types-bound-minimal-invariant-sets`.

**Statement.**

1. `G` has no similarity type system of finite size.
2. More generally, no étale groupoid with totally disconnected unit space and
   infinitely many minimal closed invariant sets has one. This covers every
   ambient groupoid that could replace `G` on the route
   `uncountably-many-simple-fp2-via-v-times-shift-restrictions`, where the
   `2^aleph_0` simple quotients come from restrictions to distinct minimal
   invariant sets.

Proof in `v-times-shift-groupoid-has-no-finite-similarity-types-proof`.

**What this kills.** A Brown-criterion proof that `A(G)` is of type FP_2
through a Stein–Farley-type complex filtered by the number of pieces dies at
cocompactness. That is the attempt suggested in
`v-times-shift-alternating-group-is-of-type-fp2`.
- The invariant is the number of similarity types, which is at least the number
  of minimal invariant sets.
- The step where every such proof dies: finitely many orbits of one-piece
  vertices.
- Heuristically, a basic piece `[u] × [w]_I` keeps its tape word `w` under
  every germ `(g, σ^k)`, so the types are indexed by words.

A surviving finiteness proof needs a filtration with a second parameter that
bounds word length, together with connectivity estimates as that parameter
grows. This does **not** refute FP_2.
