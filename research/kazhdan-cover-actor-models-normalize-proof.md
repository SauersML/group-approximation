---
rg: 2
id: kazhdan-cover-actor-models-normalize-proof
kind: route
title: Kazhdan rounding identifies the ultraproduct commutant with exact commutants, where lifted compressors act by dimension count
target: kazhdan-cover-actor-models-normalize-vertex-commutants
requires: []
artifacts:
  - research/artifacts/hl-nh-el3-compressor-2026-09-14.md
---

Notation is as in the claim. `||x||_2 = tr(x* x)^(1/2)` with `tr` normalized, and `||·||` is the
operator norm. For unitaries `u, v` and any `x`: `||u x v||_2 = ||x||_2`.

## 1. The model is a homomorphism

If `ĝ, ĝ' ∈ P^-1(g)` then `ĝ' = ĝ m` with `m ∈ N`, and

```text
||ρ_n(ĝ m) - ρ_n(ĝ)||_2 = ||ρ_n(ĝ)(ρ_n(m) - 1)||_2 = ||ρ_n(m) - 1||_2 -> 0 along U
```

by (KC). So `σ(g)` does not depend on the lift. Lifts multiply (`ĝ ĥ ∈ P^-1(gh)`) and each
`ρ_n` is multiplicative, so `σ` is a homomorphism into the unitary group of `M`.

## 2. Kazhdan inequality

Property (T) for the discrete group `Γ̂` gives a Kazhdan pair `(S, κ)`: `S ⊆ Γ̂` finite, `κ > 0`,
and every unitary representation with a unit vector moved by less than `κ` by all of `S` has a
nonzero invariant vector. For every unitary representation `π` of `Γ̂` on `H`, with `Q` the
projection onto the invariant vectors,

```text
||ξ - Qξ|| <= κ^-1 max_(s ∈ S) ||π(s)ξ - ξ||     for all ξ ∈ H.
```

Proof. `η = ξ - Qξ` lies in the orthogonal complement `H_0` of the invariant vectors, which is a
subrepresentation with no nonzero invariant vector. `π(s)ξ - ξ = π(s)η - η`. If `η ≠ 0` and
`max_s ||π(s)η - η|| < κ ||η||`, then `η/||η||` would force a nonzero invariant vector in `H_0`.

## 3. The commutant is the ultraproduct of exact commutants

- **`prod_U A_n ⊆ σ(Γ)' ∩ M`.** Each `γ ∈ Γ` has a lift `γ̂ ∈ Γ̂` since `P(Γ̂) = Γ`, and
  `σ(γ) = [ρ_n(γ̂)]`. An element `[a_n]` with `a_n ∈ A_n` commutes with `ρ_n(γ̂)` at every `n`.
- **`σ(Γ)' ∩ M ⊆ prod_U A_n`.** Let `x ∈ σ(Γ)' ∩ M` with representative `(x_n)`,
  `sup_n ||x_n|| <= C`. For `s ∈ S`, `P(s) ∈ Γ` and `σ(P(s)) = [ρ_n(s)]`, so

  ```text
  lim_U ||ρ_n(s) x_n ρ_n(s)* - x_n||_2 = ||σ(P(s)) x σ(P(s))* - x||_2 = 0.
  ```

  Apply §2 to `π_n = Ad ρ_n|Γ̂` on `H_n = (M_(d_n), <a, b> = tr(b* a))`. This is a unitary
  representation. Its invariant vectors are exactly `A_n`, and the projection onto them is the
  trace-preserving conditional expectation `E_n` onto `A_n`. So

  ```text
  ||x_n - E_n(x_n)||_2 <= κ^-1 max_(s ∈ S) ||ρ_n(s) x_n ρ_n(s)* - x_n||_2 -> 0 along U.
  ```

  Conditional expectations are contractive, so `||E_n(x_n)|| <= C`, and `x = [E_n(x_n)] ∈ prod_U A_n`.

## 4. Lifted compressors normalize at every finite stage

Fix `t ∈ T̂` and `n`, and put `u = ρ_n(t)`. Then

```text
u* A_n u = (u* ρ_n(Γ̂) u)' ∩ M_(d_n) = ρ_n(t^-1 Γ̂ t)' ∩ M_(d_n).
```

`t Γ̂ t^-1 <= Γ̂` is the same as `Γ̂ <= t^-1 Γ̂ t`, so `ρ_n(t^-1 Γ̂ t)' ⊆ ρ_n(Γ̂)'` and
`u* A_n u ⊆ A_n`. Both are finite-dimensional of the same dimension, so `u* A_n u = A_n`, and then
`u A_n u* = A_n`. This is `commutant-no-growth` applied to the representation `ρ_n` of `Ĝ`.

## 5. Normalization

By §3 and §4, `σ(P(t)) = [ρ_n(t)]` satisfies `σ(P(t)) A σ(P(t))* = A` for `A = σ(Γ)' ∩ M` and every
`t ∈ T̂`: representatives `ρ_n(t) a_n ρ_n(t)*` of conjugated elements lie in `A_n`, in both
directions. Every `σ(γ)`, `γ ∈ Γ`, commutes with `A` and so normalizes it. The unitaries of `M`
normalizing `A` form a group, and it contains `σ(Γ ∪ P(T̂))`, which generates `σ(G)`. ∎

## Calibration

- **Free covers.** Take `Ĝ` free on the elements of `G`, and lift unitary representatives of `σ(g)`.
  Relators map to `1` in the limit, and so does every product of their conjugates, so (KC) holds for
  every `σ`. The preimage of `Γ` is free, so `Γ̂` with property (T) cannot be chosen there unless
  `Γ` is trivial. The theorem is silent, as it must be.
- **II₁ stages.** Replacing `M_(d_n)` by a II₁ factor breaks §4: `u* A u ⊊ A` is possible with no
  dimension to compare. `kun-thom-wreath-factor-is-exact-nonnormalized-commutant` is a genuine
  representation of that kind with a non-normalized commutant.
- **The lift condition.** For `Γ̂ = P^-1(Γ)` the condition `t Γ̂ t^-1 <= Γ̂` follows from `N` being
  normal, but `P^-1(Γ)` contains `N` and need not have property (T). Smaller Kazhdan lifts, such as
  images of Steinberg groups over the positive ring, need the condition checked directly
  (`steinberg-actor-models-carry-no-rigid-wall-proof`).
