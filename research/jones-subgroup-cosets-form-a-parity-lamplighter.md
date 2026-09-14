---
rg: 2
id: jones-subgroup-cosets-form-a-parity-lamplighter
kind: claim
title: The cosets of Jones' subgroup in Thompson's group F form a transitive affine lamplighter over the dyadic rationals
distinct_from:
  jones-subgroup-is-stabilizer-of-odd-digit-sum-dyadics: that identifies the subgroup as the stabilizer of the odd-digit-sum dyadics; this computes the full coset space as an explicit affine action with a finite parity cocycle.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that covers Schreier graphs whose stabilizers contain an end-rigid subgroup; Jones' subgroup contains none of those, and this describes its coset graph instead.
artifacts:
  - research/artifacts/ideas-wildcards-2026-09-14.md
---

**ESTABLISHED.** Let `D` be the dyadic rationals in `(0,1)`. For `t = .a_1⋯a_m ∈ D` with `a_m = 1`, put
`ℓ(t) = m` and `p(t) = Σ a_i mod 2`. For `g ∈ F` put

`J(g) = {t ∈ D : ℓ(g t) − ℓ(t) + log₂ g'_−(t) is odd}`, where `g'_−` is the left derivative.

1. **Defects.** `J(g)` is finite. It is the set of points where `t ↦ p(t) + p(gt)` changes value, and that
   function vanishes near `0`.
2. **Cocycle.** `J(gh) = J(h) Δ h⁻¹J(g)`, and `J(g) = ∅` exactly when `g ∈ \vec F` (Jones' oriented subgroup).
3. **Affine model.** With `J_L(g) = J(g⁻¹)`, the rule `g ⋆ E = gE Δ J_L(g)` is an action of `F` on finite subsets
   of `D`. It is pulled back from the affine action of `P_f(D) ⋊ F` along `g ↦ (J_L(g), g)`. The map
   `g\vec F ↦ J_L(g)` is an `F`-equivariant bijection onto the orbit of `∅`.
4. **Transitivity.** Every finite `E ⊂ D` equals `J(g)` for some `g`. So `F/\vec F ≅ (P_f(D), ⋆)` as `F`-sets. With
   the standard generators: `x_0 ⋆ E = x_0E Δ {1/2}` and `x_1 ⋆ E = x_1E Δ {3/4}`.
5. **Corollary.** Every set `S Δ (A ∩ D)`, with `S` the odd-digit-sum dyadics and `A` a finite union of intervals
   `[a,b)` with `a ∈ D` and `b ∈ D ∪ {1}`, is an `F`-translate of `S`. Its stabilizer is conjugate to `\vec F`.

**Scope.** Unreviewed. No novelty is claimed (partial literature check, recorded in the artifact).

Proof route: `jones-subgroup-parity-lamplighter-proof`.
