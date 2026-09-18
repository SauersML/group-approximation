---
rg: 2
id: rational-projective-full-groups-fp-via-thumann-operad-finiteness
kind: route
title: If the operad of unimodular dissections has finite type, Thumann's theorem makes the integral projective full group of type F-infinity, hence finitely presented
target: rational-projective-full-groups-are-finitely-presented
requires:
  - unimodular-dissection-operad-has-finite-type
---

Lane bh-free-54, 2026-09-18. Thumann's theorem was read at source. The
verification of its hypotheses below is lane reasoning and not independently
reviewed.

## The imported theorem

W. Thumann, *Operad groups and their finiteness properties*, arXiv:1409.1085.
Theorem `41762` in the source (statement read verbatim in the LaTeX source):

> Let `𝒪` be a planar or symmetric or braided operad with transformations. Assume
> that `𝒪` has only finitely many colors and is color-tame. Assume further that `𝒪`
> satisfies the cancellative calculus of fractions, is of finite type and `ℐ(𝒪)` is
> a groupoid of type `F_∞^+`. Then for every object `X` in `𝒮(𝒪)` the operad group
> `π_1(𝒪, X)` is of type `F_∞`.

The terms, as defined in the source:
- **Transformations** are the invertible degree-1 operations.
- `𝒯𝒞(𝒪)` is the poset of transformation classes. `𝒯𝒞*(𝒪)` is the part of degree
  at least 2.
- The *very elementary* classes are the minimal elements of `𝒯𝒞*(𝒪)`
  (Definition `13449`).
- The *elementary* classes form the *spine* of `𝒯𝒞*(𝒪)` (Definition `24121`). The
  spine of a graded poset is the smallest set containing the minimal elements such
  that every element outside it has a greatest element of the set below it
  (Definition `79040`). It is built by iterating minimal common upper bounds of
  pairs (Construction `45209`).
- *Finite type* means finitely many elementary classes. *Finitely generated* means
  finitely many very elementary classes (Definition `26536`).
- *Color-tame* holds automatically for a monochromatic operad with one higher-degree
  operation (remark after Definition `77101`).
- Mono and epi operations of a suboperad of `End(TOP, ⊔)` give right and left
  cancellation (text before the square/triangle example).

## The operad

Fix `m ≥ 1` and the clopen `Δ ⊂ Ŝ_m`. Let `𝒪_m` be the suboperad of
`End(TOP, ⊔)` with the single color `Δ` defined as follows.
- An operation of degree `k` is a tuple `(g_1|_Δ, …, g_k|_Δ)`, where
  `g_i ∈ GL_{m+1}(Z)` and the `g_iΔ` form a unimodular dissection of `Δ`.
- Composition is substitution. `(g_i)∘(h_{i,j}) = (g_i h_{i,j})` is again a
  dissection, since `g_i` carries a dissection of `Δ` onto one of `g_iΔ`.

## Hypotheses

1. **One color; color-tame.** The operad is monochromatic and `𝒪_m(2) ≠ ∅` (the
   stellar split at `e_0 + e_1`).
2. **`ℐ(𝒪_m)` is finite.** The degree-1 operations are the `g ∈ GL_{m+1}(Z)` with
   `gΔ = Δ`. These are the permutation matrices, a group isomorphic to `S_{m+1}`.
   Finite groups are `F_∞^+` (remark after the source's definition).
3. **Cancellative calculus of fractions.**
   - **Cancellation.** Every operation is mono (disjoint images, injective) and epi
     (images cover), so both cancellation properties hold by the source's remark.
   - **Equalization.** It is trivial: if `γ∘α = γ∘β`, then `α = β`, because `γ` is
     injective.
   - **Square filling.** Given two dissections `(g_i)` and `(g'_j)`:
     - intersect the pieces;
     - triangulate each rational polyhedral cone `g_iΔ ∩ g'_jΔ`;
     - resolve each simplicial cone unimodularly, one cone at a time. T-junctions
       are allowed, so no compatibility across faces is needed.
     - The result `(r_l)` refines both. On `g_iΔ`, the pieces pull back under `g_i`
       to a dissection `ψ_i` of `Δ` with `g_i ψ_i = (r_l)_{l ⊂ i}`. Similarly `ψ'_j`
       on the other side. So `(g_i)∘(ψ_i) = (g'_j)∘(ψ'_j)` up to reordering inputs,
       which the symmetric structure absorbs.
4. **Transformation classes are unlabelled dissections.**
   - Two labellings of a piece differ by `S_{m+1}`, and inputs can be permuted. So a
     transformation class is exactly the set of pieces `{g_iΔ}`.
   - `[θ] ≤ [θ']` holds exactly when the dissection of `θ'` refines that of `θ`. So
     `𝒯𝒞*(𝒪_m)` is the poset of nontrivial unimodular dissections of `Δ` under
     refinement, graded by the number of pieces.
   - Its minimal elements are the *prime* dissections: those with no set of at
     least 2, but not all, pieces whose union is a unimodular cone.
   - **Why prime means minimal.** If such a set exists, merging it gives a proper
     nontrivial coarsening. Conversely, a proper nontrivial coarsening has a piece
     that is a union of at least 2 but not all pieces.
5. **Finite type** is the premise `unimodular-dissection-operad-has-finite-type`.

## The operad group is `𝒯_m`

- An element of `π_1(𝒪_m, Δ)` is a fraction `θ'∘θ^{-1}`, with `θ, θ' ∈ 𝒪_m(k)`.
  The calculus of fractions gives fractions for the fundamental groupoid
  (Gabriel–Zisman).
- It acts on `Δ` as the homeomorphism sending `g_iΔ` to `g'_iΔ` by `g'_i g_i^{-1}`.
- **Faithful.** The operations are the maps themselves, so `θ'∘θ^{-1} = id` forces
  `θ' = θ`.
- **Image.** Every element of `[[𝒢|_Δ]]` is piecewise `GL_{m+1}(Z)` on a clopen
  partition. That partition refines to a unimodular dissection, whose images are
  again unimodular. So the image is `[[𝒢|_Δ]]`.
- **Conclusion.** `π_1(𝒪_m, Δ) ≅ [[𝒢|_Δ]]`. By clopen transitivity (§4 of
  `closed-mcg-rational-projective-full-group-proof`), this is isomorphic to
  `𝒯_m = [[𝒢]]`.

This matches how the source treats its own examples: cube cutting operads give
`nV`, and ultrametric ball operads give local similarity groups.

## Conclusion

If `unimodular-dissection-operad-has-finite-type` holds for `m`, then `𝒯_m` is of
type `F_∞`, and in particular finitely presented.
- At `m = 1` the premise holds: every nontrivial Farey dissection refines the
  mediant split, so the spine is that single split. This recovers finite
  presentation of `𝒯_1 ≅ V_{2,4}(⟨σ⟩)` (`rank-one-rational-projective-full-group-is-flip-v`)
  and upgrades it to `F_∞`.
- No weak or strong factorization theorem is needed on this route. The
  connectivity that such theorems would supply is internal to Thumann's proof,
  given finite type.

## Lesson for general BH

- **Nothing about the group enters.** Thumann's theorem turns finite presentation
  (indeed `F_∞`) of any full group of a geometric subdivision groupoid into a
  finite-type condition on its operad of dissections. So a host problem for
  Boone–Higman can be posed and tested in this form, independent of the group being
  embedded.
- **The precise target.** For groups with faithful piecewise-integral-projective
  actions, BH reduces to one question: does the unimodular dissection operad, or a
  suboperad stable under the group, have finite type?
- **A search-ready test.** Its minimal elements are the prime dissections, testable
  by the exact volume criterion of
  `unimodular-dissections-have-egyptian-fraction-volumes`.
