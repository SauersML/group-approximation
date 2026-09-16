---
rg: 2
id: dihedral-sturmian-groupoid-algebra-is-no-subshift-ring-proof
kind: route
title: The doubled rotation T′ is minimal when T² is, the Steinberg algebra is the D_∞-crossed product, and its K_1 is 4-torsion while K_1 of every minimal Z-crossed product is Z; Sturmian T² is minimal by uniform recurrence of rotation by 2α
target: dihedral-sturmian-groupoid-algebra-is-no-subshift-ring
requires:
  - dihedral-cantor-crossed-product-k1-has-exponent-four
  - crossed-products-are-transformation-steinberg-algebras
artifacts:
  - research/artifacts/dihedral-cantor-k1-exponent-four-2026-09-16.md
---

- **Step 1 (the action).** `s² (x,e) = (R²x, e) = (x,e)`, and
  `sT′s(x,e) = sT′(Rx, e+1) = s(TRx, e) = (RTRx, e+1) = (T^(−1)x, e+1) = T′^(−1)(x,e)`.
- **Step 2 (T′ minimal).** Let `M ⊆ X′` be nonempty, closed and `T′`-invariant, and put `M_e = {x : (x,e) ∈ M}`.
  - Then `TM_0 = M_1` and `TM_1 = M_0`, so `M_0 ≠ ∅` and `T²M_0 = M_0`.
  - `T²` minimal gives `M_0 = X`, hence `M_1 = X` and `M = X′`.
  - `X′` is a Cantor space and `T′` has no periodic points, so `(X′,T′)` is an infinite minimal Cantor system. Artifact
    §4, Lemma 4a.
- **Step 3 (item 1).** `A_(F_2)(G_D) ≅ LC(X′,F_2) ⋊ D_∞` by `crossed-products-are-transformation-steinberg-algebras`.
  Apply `dihedral-cantor-crossed-product-k1-has-exponent-four` with `(Y,S,P) = (X′,T′,s)`: `M_1(A) ≇ M_n(R_Y)`.
  Artifact §4, Corollary 4.
- **Step 4 (Sturmian inputs).** Artifact §4, Lemma 4b.
  - `Tx^θ = x^(θ+α)`, and the generic codings (`θ ∉ Z + αZ`) are dense in `X_α`, by right-continuity of
    `1_([1−α,1))`.
  - **Uniform recurrence.** For `β ∈ {α, 2α}` and an open interval `J`, compactness of `R/Z` and density of forward
    rotation orbits give `K` with `R = ⋃_(k≤K)(J − kβ + Z)`. So every point of `X_α` enters every generic cylinder
    under `T^(β/α)` within `K` steps. Hence `T` and `T²` are minimal.
  - **Infinite.** Distinct generic `θ mod 1` give distinct codings, because two distinct arcs of length `α` have a
    symmetric difference with nonempty interior. So `X_α` is uncountable. An isolated point would make `X_α` a single
    countable orbit, so `X_α` is a Cantor space.
  - **Reversal.** For generic `θ`, with `t = {−θ + nα} ∉ {0, α}`: `(Rx^θ)_n = 1` iff `t ∈ (0,α)` iff
    `x^(1−α−θ)_n = 1`. So `R` maps generic codings to generic codings, and `R(X_α) = X_α` by continuity. The identity
    `RTR = T^(−1)` is a coordinate check, and `T^jR` also satisfies both relations.
- **Step 5 (Sturmian case).** Steps 3 and 4 give item 2 and the consequence for decider (c). ∎
