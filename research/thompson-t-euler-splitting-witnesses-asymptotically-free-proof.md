---
rg: 2
id: thompson-t-euler-splitting-witnesses-asymptotically-free-proof
kind: route
title: Push the almost invariant densities to Sub(T), identify every limit IRS through the character simplex of T, and remove the global fixed set with the Euler normalization
target: thompson-t-euler-splitting-witnesses-are-asymptotically-free
requires:
  - no-proper-character-groups-avoid-amenable-orbit-full-groups
  - lifted-thompson-t-perfect-centre-cubically-elliptic
---

Notation as in the target. The action is taken Borel. A nonsingular action of a countable group given
only modulo null sets has a Borel pointwise model (Mackey's point realization), and changing the model
changes `Fix(g)` only by a null set.

**Imports.**
- (I1) `T` is simple and infinite. This is classical (Cannon–Floyd–Parry, Section 5), the same
  assumption under which item 4 of `no-proper-character-groups-avoid-amenable-orbit-full-groups` is stated.
- (I2) Item 4 of `no-proper-character-groups-avoid-amenable-orbit-full-groups`: `T` has no proper
  characters. The definition there is verbatim: "its only indecomposable characters are the identity and
  the regular one", that is, `1` and `δ_e`.
- (I3) Item 2 of `lifted-thompson-t-perfect-centre-cubically-elliptic`: `T̄ = [T̄, T̄]`, so
  `Hom(T̄, R) = 0`.
- (I4) Choquet's theorem for metrizable compact convex sets (Phelps, *Lectures on Choquet's theorem*,
  §3): every point is the barycenter of a probability measure on the extreme points.
- Standard facts on direct integrals and GNS uniqueness. Nothing else is used.

The Koopman representation is `κ(g)ξ = (d g_*μ / dμ)^{1/2} · ξ ∘ g^{-1}`. Almost invariance means
`‖κ(g)ξ_n − ξ_n‖₂ → 0` for every `g ∈ T`.

## Step 1. The densities are almost invariant in total variation

`|κ(g)ξ|² μ = g_*(|ξ|² μ)`, by the change of variables that defines `κ`. So, by Cauchy–Schwarz,

```text
‖g_*ν_n − ν_n‖_TV ≤ ∫ | |κ(g)ξ_n|² − |ξ_n|² | dμ
                 ≤ ‖κ(g)ξ_n − ξ_n‖₂ (‖κ(g)ξ_n‖₂ + ‖ξ_n‖₂) = 2 ‖κ(g)ξ_n − ξ_n‖₂ → 0.
```

## Step 2. Stabilizer laws are almost conjugation invariant

Give `Sub(T) ⊆ {0,1}^T` the product topology. It is compact and metrizable, and the cylinders
`C_g = {K : g ∈ K}` are clopen.
- The map `Stab : X → Sub(T)` is Borel, because `Stab^{-1}(C_g) = Fix(g)` is Borel for a Borel action.
- `Stab(gx) = g Stab(x) g^{-1}`. So with `c_g(K) = gKg^{-1}`, a homeomorphism of `Sub(T)`, and
  `λ_n = Stab_* ν_n`, we get `(c_g)_* λ_n = Stab_*(g_* ν_n)`.
- Hence `‖(c_g)_* λ_n − λ_n‖_TV ≤ ‖g_*ν_n − ν_n‖_TV → 0` by Step 1.

Let `λ` be the weak* limit of a subsequence `λ_{n_k}`. For continuous `f` on `Sub(T)`,
`|∫ f∘c_g dλ_n − ∫ f dλ_n| ≤ ‖f‖_∞ ‖(c_g)_*λ_n − λ_n‖_TV → 0`. So `λ` is conjugation invariant, an
IRS of `T`. For every clopen `C ⊆ Sub(T)`, `λ(C) = lim_k λ_{n_k}(C)`.

## Step 3. The global fixed set is null, so `λ{T} = 0`

Fix a finite generating set `S` of `T` (for example `T = ⟨F, l⟩` with `F = ⟨a, b⟩`, as recalled in
`lodha-simple-group-s-is-two-generated-proof`). Then `{T} = ⋂_(s ∈ S) C_s` is clopen, and
`Stab^{-1}{T} = Fix(T) := ⋂_(s ∈ S) Fix(s)`.

**Claim: `μ(Fix(T)) = 0`.**
- `T̄` is countable. So there is a conull `X_0 ⊆ X` on which `β(gh, x) = β(g, hx) + β(h, x)` holds for
  all `g, h ∈ T̄`, and `β(z, x) = 1`.
- For `x ∈ Fix(T) ∩ X_0`, every `h ∈ T̄` fixes `x`, because `T̄` acts through `T`. So
  `g ↦ β(g, x)` is a homomorphism `T̄ → R` sending `z` to `1`. This contradicts (I3).
- Hence `Fix(T) ∩ X_0 = ∅`.

Since `ν_n ≪ μ`, `ν_n(Fix(T)) = 0` for all `n`, and by Step 2, `λ{T} = lim_k ν_{n_k}(Fix(T)) = 0`.

## Step 4. The character of `λ` is `a + (1 − a)δ_e`

Put `φ(g) = λ(C_g)`.
- **Positive definite.** For a subgroup `K`, `1_K(g) = ⟨ρ_K(g)δ_K, δ_K⟩`, where `ρ_K` is the
  quasi-regular representation on `ℓ²(T/K)`. So `1_K` is positive definite. `φ = ∫ 1_K dλ(K)` is an
  integral of positive definite functions, with Borel integrand in `K` for each fixed `g`.
- **Class function.** `φ(hgh^{-1}) = λ(c_h(C_g)) = φ(g)` by invariance of `λ`.
- **Normalized.** `φ(e) = 1`.

So `φ` is a character of `T`. The characters of the countable group `T` form a compact convex metrizable
subset of the unit ball of `ℓ∞(T)` in the pointwise topology. By (I2) its extreme points, the
indecomposable characters, are `1` and `δ_e`. By (I4) there is `a ∈ [0, 1]` with

```text
φ = a · 1 + (1 − a) δ_e,   that is,   λ(C_g) = a for every g ≠ e.            (4.1)
```

## Step 5. `a = λ{T}`

**The representation.**
- Let `π = ∫^⊕ ρ_K dλ(K)` on `H = ∫^⊕ ℓ²(T/K) dλ(K)`. The measurable structure is given by the
  functions `f(K, t)` on `Sub(T) × T` that are constant on the cosets `tK`.
- Let `ξ(K) = δ_K`. Then `⟨π(g)ξ, ξ⟩ = ∫ 1[gK = K] dλ(K) = φ(g)`.

**Invariant vectors of `π`.**
- `T` is countable. So `η ∈ H` is `π(T)`-invariant iff `η(K) ∈ ℓ²(T/K)^T` for `λ`-almost every `K`.
- A `T`-invariant vector in `ℓ²(T/K)` is a constant function, so it is nonzero only when `T/K` is finite.
- By (I1), a finite-index `K` has a normal core of finite index, which is `T`. So `K = T`.
- Hence `H^T = {η : η(K) = 0 for K ≠ T}`, and the projection `P` onto `H^T` satisfies
  `‖Pξ‖² = λ{T}`.

**The same norm computed from `φ`.**
- Let `H_ξ` be the cyclic subspace of `ξ`, with projection `Q ∈ π(T)'`.
- Every unitary in `π(T)'` preserves `H^T`, so `P ∈ π(T)''` and `PQ = QP`.
- Therefore `Pξ ∈ H_ξ` is the projection of `ξ` onto `(H_ξ)^T`, and its norm depends only on the cyclic
  representation `(H_ξ, π, ξ)`, that is, only on `φ`, by GNS uniqueness.
- Model `φ` by `ρ_0 = 1 ⊕ λ_T` on `C ⊕ ℓ²(T)` with `ξ_0 = (√a, √(1−a) δ_e)`. Then
  `⟨ρ_0(g)ξ_0, ξ_0⟩ = a + (1 − a)δ_e(g) = φ(g)`.
- `T` is infinite, so `(C ⊕ ℓ²(T))^T = C ⊕ 0`. The same commutation argument puts the projection
  `(√a, 0)` of `ξ_0` onto it inside the cyclic subspace of `ξ_0`, so the invariant part of `ξ_0` has
  norm squared `a`.
- Hence `a = ‖Pξ‖² = λ{T}`.

## Step 6. Conclusion

- **Item 1.**
  - By Steps 3 and 5, `a = 0`. By (4.1), `λ(C_g) = 0` for every `g ≠ e`. Since `T` is countable,
    `λ`-almost every `K` contains no `g ≠ e`, so `λ = δ_{e}`.
  - Every subsequence of `(λ_n)` has a further subsequence converging to `δ_{e}`, so `λ_n → δ_{e}`
    weak*.
  - Because `C_g` is clopen, `ν_n(Fix g) = λ_n(C_g) → δ_{e}(C_g) = 0` for `g ≠ e`. For finite
    `P ⊆ T \ {e}`, the union bound gives `ν_n{Stab ∩ P ≠ ∅} ≤ Σ_(g ∈ P) ν_n(Fix g) → 0`.
  - Conversely, suppose `ν_n(Fix g) → 0` for all `g ≠ e`. Then every weak* limit point `λ'` of
    `(λ_n)` has `λ'(C_g) = 0` for `g ≠ e`, so `λ' = δ_{e}`. By compactness `λ_n → δ_{e}`, which gives
    the stated equivalence.
- **Item 2.** If `μ` is an invariant probability measure, the constant vectors `ξ_n = 1` are invariant.
  Item 1 applied to them gives `μ(Fix g) = 0` for `g ≠ e`.
- **Item 3.**
  - Let `I` be a nonempty open arc. Choose a dyadic interval `J = [c, c + 2^{-k}]` with `J ⊂ I`, and a
    nontrivial `f ∈ F`, for instance `x_0`. The conjugate of `f` by the affine map `[0,1] → J`, extended
    by the identity, is piecewise linear with dyadic breakpoints and slopes powers of 2. So it is an
    element `g ≠ e` of `F ≤ T` supported in `J`.
  - If `K(x) ∩ I = ∅`, then `S^1 \ J` is an open neighbourhood of `K(x)` on which `g` is the identity.
    So `x ∈ Fix(g)`, and `ν_n{K(x) ∩ I = ∅} ≤ ν_n(Fix g) → 0`.
  - For `|K(x)| ≤ N`, take `N + 1` pairwise disjoint arcs: one of them misses `K(x)`.
  - For `ε`-density, take the finitely many arcs `(jε/2, (j+1)ε/2)` for `0 ≤ j < 2/ε`. If `K(x)` misses
    an open arc of length `2ε`, it misses one of them.
  - In each case the set lies in a finite union of sets whose `ν_n`-mass tends to `0`. ∎

**Remark on the Euler normalization.** It enters only in Step 3. Without it, the same argument gives
`ν_n(Fix g) − ν_n(Fix T) → 0`, which is the measure analogue of item 2 of
`thompson-v-amenable-actions-are-free-off-fixed-points`.
