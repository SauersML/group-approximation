---
rg: 2
id: bauer-gamma-failure-localizes-proof
kind: route
title: Local triviality away from Z(M) is Evington--Pennig, and finite-dimensional neighbourhoods are trivial by Ozawa
target: bauer-gamma-failure-localizes-to-infinite-dim-point
requires:
  - r-fibre-w-star-bundle-locally-trivial-is-trivial
  - r-fibre-w-star-bundle-finite-dim-base-is-trivial
  - bauer-uniform-gamma-iff-trivial-tracial-bundle
artifacts:
  - research/artifacts/tw-bundle-hunter-bundle-localization-2026-09-12.md
---

1. **Closedness.**  A closed neighbourhood of `x` is a closed neighbourhood of
   every point of its interior, so the complements of `Z(M)` and `K_inf` are
   open.
2. **Trivial ⟹ `Z(M) = ∅`.**  If `M ≅ C_σ(K,R)`, restricting functions gives
   `C_σ(Y,R)` over each closed `Y`.  Surjectivity comes from Dugundji's
   extension theorem, applied to the unit ball of `R` with the 2-norm, a convex
   subset of a normed space.
3. **`Z(M) = ∅` ⟹ trivial.**  Empty `Z(M)` is local triviality, and
   `r-fibre-w-star-bundle-locally-trivial-is-trivial` applies.
4. **`Z(M) ⊆ K_inf`.**  Let `Y` be a closed neighbourhood of `x` with
   `dim Y < ∞`.
   - The restriction `M_Y = M/I_Y`, with `I_Y` the sections whose conditional
     expectation of `a*a` vanishes on `Y` (Evington--Pennig, Definition 2.8 and
     Proposition 2.9), is a W*-bundle over `Y`.  Its fibre at `y ∈ Y` is the
     fibre of `M` at `y` (their diagrams (2.13)--(2.14)), hence `R`.
   - The restriction map is the quotient map, so it is onto, and it is
     contractive for the uniform 2-norms.  The image of a countable strictly
     dense subset of `M` is strictly dense in `M_Y`, so `M_Y` is strictly
     separable.
   - `r-fibre-w-star-bundle-finite-dim-base-is-trivial` makes `M_Y` trivial, so
     `x ∉ Z(M)`.
5. **`K_inf = ∅` ⟺ `dim K < ∞`.**  If every point has a finite-dimensional
   closed neighbourhood, finitely many interiors cover `K`.  The finite sum
   theorem for closed subsets of metrizable spaces then bounds `dim K`.  The
   converse is monotonicity of covering dimension on closed subsets.
6. **Algebra form.**  By `bauer-uniform-gamma-iff-trivial-tracial-bundle`, the
   strict closure `M` of `A` is an `R`-fibre bundle over `∂_e T(A)`, nontrivial
   when Gamma fails.  Take `τ_0 ∈ Z(M)`, which is nonempty by step 3.  Every
   closed neighbourhood `Y` of `τ_0` has `M_Y` nontrivial, which is condition
   (ii) of Ozawa's Theorem 15 failing for `M_Y`.  Step 4 shows `Y` is
   infinite-dimensional.

What to check in review: Ozawa's "continuous W*-bundle" and the
Evington--Pennig W*-bundle are the same notion.  Evington--Pennig's
introduction applies Ozawa's Corollary 16 to their bundles, and step 4 relies
on that.
