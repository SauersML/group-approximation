---
rg: 2
id: iid-generators-not-dense-at-positive-rokhlin-supremum-proof
kind: route
title: Sub-additivity bounds how close a generator can be to a small factor, and Bowen's weak isomorphism puts i.i.d. partitions of every distribution there
target: iid-generators-not-dense-at-positive-rokhlin-supremum
requires:
  - seward-rokhlin-entropy-subadditivity
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - nonamenable-bernoulli-shifts-are-weakly-isomorphic
---

Notation as in the target. For a finite `W ⊆ G` and a partition `ζ`, `ζ^W = ∨_(g in W) g·ζ`. `𝒫_A` is the
partition of `X` by the `A`-part of the coordinate at `1_G`, so `𝒜 = σ-alg_G(𝒫_A)`.

**Step 0: two values.** `X` is ergodic. By item 1 of `seward-per-group-rokhlin-entropy-of-bernoulli-shifts`,
`h^Rok_G(X) = min(H(κ), s) = r`. The factor associated with `𝒜` is the Bernoulli shift `(A^G, p^G)`, whose
Rokhlin entropy is `min(a, s)`.

**Step 1: item 1.** Let `γ` be a generating partition and `ε > 0`. Choose a generating partition of the
factor `(A^G, p^G)` with Shannon entropy below `min(a, s) + ε`, and let `η` be its pull-back to `X`. Then
`𝒜 ⊆ σ-alg_G(η)`, and `σ-alg_G(γ) ∨ 𝒜 = B(X)` because `γ` generates. The two-step form of
`seward-rokhlin-entropy-subadditivity` gives

    r = h^Rok_G(X) <= H(η) + H(γ | 𝒜) < min(a, s) + ε + H(γ | 𝒜).

Let `ε → 0`. If `ξ ⊆ 𝒜`, then `σ-alg(ξ) ⊆ 𝒜` and `H(γ | ξ) >= H(γ | 𝒜)`.

**Step 2: item 2.** The bases `(A, p)` and `(L, λ)` are nontrivial, because `a > 0` and `H(λ) > 0`. By
`nonamenable-bernoulli-shifts-are-weakly-isomorphic` there is an equivariant `Φ : A^G → L^G` with
`Φ_* p^G = λ^G`. Let `π_A : X → A^G` be the projection and `ξ_ℓ = {x : Φ(π_A x)(1_G) = ℓ}`.
- Since `Φ(π_A(g^-1 x)) = g^-1·Φ(π_A x)`, the translate `g·ξ` partitions `X` by the value `Φ(π_A x)(g)`.
- These values are independent with law `λ`, because `Φ ∘ π_A` pushes `µ` to `λ^G`.
- `Φ ∘ π_A` is `𝒜`-measurable, so `ξ ⊆ 𝒜`.

**Step 3: item 3.** Let `D = {γ ≠ ξ}`, so `µ(D) = δ`. Off `D` the partition `γ` equals `ξ`. On `D` it takes one
of the `|L| − 1` other labels. So

    H(γ | ξ) <= H({D, X \ D}) + H(γ | ξ ∨ {D, X \ D}) <= h_2(δ) + δ log(|L| − 1).

With `a < s`, Step 1 gives `min(a, s) = a` and `H(γ | ξ) >= r − a`, and `r − a > 0` because `H(κ) > a`.
The bound `h_2(δ) + δ log(|L| − 1)` tends to `0` with `δ`. So some `δ_0 > 0` has no generating partition within
`d`-distance `δ_0` of `ξ`. By Step 2, `ξ ∈ Ind_λ(X)`, so the `δ_0`-ball around `ξ` in `Ind_λ(X)` contains no
generating partition.

**Step 4: item 4.** Put `r_λ = min(H(λ), s)`, so `r_λ > a`. On `L^G × K^G` let `ℓ` be the partition by the
`L`-coordinate at `1_G` and `𝒫_A'` the partition by the `A`-part of the `K`-coordinate at `1_G`.
- **Continuity.** For finite `W`, `ν ↦ H_ν(ℓ | (𝒫_A')^W)` on `J` depends on finitely many cylinder measures,
  so it is continuous.
- **At `ν_ξ`.** The map `x ↦ ((g ↦ ξ(g^-1 x)), x)` pushes `µ` to `ν_ξ` and pulls `ℓ` back to `ξ` and `𝒫_A'`
  back to `𝒫_A`. Since `ξ ⊆ 𝒜`, martingale convergence of conditional entropy along finite `W_n ↑ G` gives
  a finite `W` with `H_(ν_ξ)(ℓ | (𝒫_A')^W) < (r_λ − a)/2`.
- **The neighbourhood.** `U = {ν ∈ J : H_ν(ℓ | (𝒫_A')^W) < (r_λ − a)/2}` is open and contains `ν_ξ`.

Let `ν ∈ U` be a joining in which the `L`-coordinates determine the `K`-coordinates.
- `(L^G × K^G, ν)` is isomorphic to `(L^G, λ^G)` through the first projection. So it is ergodic, `ℓ` generates,
  and its Rokhlin entropy is `r_λ`.
- The `K`-marginal of `ν` is `κ^G`, so `σ-alg_G(𝒫_A')` is a factor isomorphic to `(A^G, p^G)`, of Rokhlin
  entropy `min(a, s) = a`.
- Step 1 inside this system gives

      r_λ <= a + H_ν(ℓ | σ-alg_G(𝒫_A')) <= a + H_ν(ℓ | (𝒫_A')^W) < a + (r_λ − a)/2 < r_λ,

  a contradiction.

An isomorphism joining, and the joining `(id × Φ)_* λ^G` of a factor map `Φ : L^G → K^G`, are joinings in which
the `L`-coordinates determine the `K`-coordinates.
