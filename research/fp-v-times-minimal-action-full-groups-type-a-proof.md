---
rg: 2
id: fp-v-times-minimal-action-full-groups-type-a-proof
kind: route
title: Topological full groups are full, and the clopen equivalence lemma makes their local maps clopen transitive
target: fp-v-times-minimal-action-full-groups-have-type-a-actions
requires:
  - v-times-minimal-action-groupoid-clopens-are-equivalent
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
  - v-times-ample-full-groups-are-generated-by-transpositions
---

Notation as in the target, with `D = F(T)`. For a compact open bisection `B`
write `τ_B : s(B) -> r(B)` for the induced homeomorphism.

**Step 0. `Y` is a Cantor space.** `C` is a Cantor space and `X` is nonempty,
compact, metrizable and totally disconnected. So `C × X` is compact, metrizable
and totally disconnected, and it has no isolated points because `C` has none.

**Step 1. `D` is full.** Let `h` be a homeomorphism of `Y` that is D-local.
- By compactness there is a finite clopen partition `Y = ⊔_i N_i` and elements
  `g_i = τ_{B_i} ∈ D` with `h = g_i` on `N_i`. Refine open neighbourhoods to
  clopen ones and disjointify.
- `B_i|N_i = B_i ∩ s^{-1}(N_i)` is a compact open bisection from `N_i` onto
  `h(N_i)`.
- The sources `N_i` partition `Y`, and so do the ranges `h(N_i)`, since `h` is a
  bijection. So `B = ⊔_i B_i|N_i` is a compact open bisection with
  `s(B) = r(B) = Y` and `τ_B = h`. Hence `h ∈ D`.

**Step 2. Local maps are clopen transitive.** Let `U, U'` be nonempty clopen sets.
By `v-times-minimal-action-groupoid-clopens-are-equivalent` there is a compact
open bisection `B` from `U` onto `U'`. We show `τ_B` is D-local.
- Fix `p ∈ U`. Choose distinct points `q ≠ p` and `q' ≠ τ_B(p)`, possible by
  Step 0.
- Choose a clopen `N` with `p ∈ N ⊆ U`, `q ∉ N` and `τ_B^{-1}(q') ∉ N`. Then `N`
  and `τ_B(N)` are proper nonempty clopen sets.
- The lemma again gives a compact open bisection `B'` from `Y \ N` onto
  `Y \ τ_B(N)`. Then `B|N ⊔ B'` is a compact open bisection with source and
  range `Y`. Its homeomorphism is an element of `D` agreeing with `τ_B` on `N`.

**Step 3. Conclusion.** Steps 0, 1 and 2 are hypotheses 1 and 2 of
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`, and hypothesis 3
is the assumption. That claim gives the type (A) action and every stated
consequence.

**Last paragraph of the target.** Its equality `F(T) = A(T)` is the theorem of
`v-times-ample-full-groups-are-generated-by-transpositions`, which applies to
every ample Hausdorff `H` with compact totally disconnected unit space. `Λ ⋉ X`
is such a groupoid. ∎
