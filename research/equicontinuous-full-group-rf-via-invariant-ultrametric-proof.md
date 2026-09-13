---
rg: 2
id: equicontinuous-full-group-rf-via-invariant-ultrametric-proof
kind: route
title: An invariant ultrametric makes every full-group element permute small balls, and the ball permutations separate
target: equicontinuous-action-full-group-fg-subgroups-are-rf
requires: []
artifacts:
  - research/artifacts/solve-fp-amenable-nonfree-hosts-2026-09-13.md
---

## Why sufficient

1. **Invariant ultrametric.**
   - `X` is a Cantor space, so it has a compatible ultrametric `d`. Put
     `d'(x, y) = sup_λ d(λx, λy)`.
   - It is a supremum of ultrametrics, so it is an ultrametric, and it is `Λ`-invariant.
   - Taking `λ = e` gives `d ≤ d'`. Equicontinuity gives, for each `ε`, a `δ` with
     `d(x, y) < δ ⇒ d'(x, y) ≤ ε`.
   - So the identity `(X, d) -> (X, d')` is continuous. Since `X` is compact, `d'` is
     compatible.
   - Every `λ` is an isometry of `d'`.
2. **Balls.** For `r > 0`, the closed `d'`-balls of radius `r` are clopen, and two of them
   are equal or disjoint. By compactness they form a finite partition `𝔅_r`. An isometry
   maps `B(x, r)` onto `B(λx, r)`, so `Λ` permutes `𝔅_r`.
3. **Full-group elements permute small balls.**
   - Let `g ∈ [[Λ ~ X]]`. Its cocycle `c_g` is continuous into a discrete group, so its
     level sets form a finite clopen partition of `X`.
   - A finite clopen partition of a compact ultrametric space has a positive Lebesgue
     number `r_g`. Every ball of radius `r ≤ r_g` lies in one level set.
   - If `c_g = λ` on `B`, then `g(B) = λ(B)` is a ball of radius `r`.
   - `g` is a bijection of `X` mapping each ball of `𝔅_r` onto a ball of `𝔅_r`, so it
     permutes `𝔅_r` for every `r ≤ r_g`.
4. **The subgroup.**
   - Let `Γ = <g_1, ..., g_k>` and `r_0 = min_i r_{g_i}`. Each `g_i` permutes `𝔅_r` for
     `r ≤ r_0`, and so does its inverse.
   - So every element of `Γ` permutes `𝔅_r` for every `r ≤ r_0`. This gives
     homomorphisms `φ_n : Γ -> Sym(𝔅_{r_0/2^n})` with finite image.
5. **Separation.**
   - Suppose `γ` lies in every `ker φ_n`, and take `x ∈ X`. Then `γ` maps the ball of
     radius `r_0/2^n` about `x` to itself.
   - So `d'(γx, x) ≤ r_0/2^n` for all `n`, and `γx = x`. Hence `γ = e`.
   - So the finite-index normal subgroups `ker φ_n` intersect trivially, and `Γ` is
     residually finite.
6. **Simple groups.** A residually finite simple group is finite: a nontrivial element
   survives in some finite quotient, whose kernel is a proper normal subgroup, hence trivial.
   So a finitely generated infinite simple group is not residually finite, and by step 5 it
   is not a subgroup of `[[Λ ~ X]]`.
