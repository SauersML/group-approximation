---
rg: 2
id: ghb7-instability-via-visible-central-extension
kind: route
title: A visible Kazhdan central Z-extension of a finite-index subgroup makes GHB_2(7) flexibly unstable
target: ghb7-is-not-flexibly-hs-stable
requires:
  - ghb7-finite-index-z-extension-center-survives
  - cckw-ghb2-kms-group-structure
  - bdhv-central-extension-property-t
  - kazhdan-cover-models-round-iff-kernel-fixed-mass-one
  - flexible-hs-stability-descends-to-retracts-finite-index
---

**Derivation, conditional on the open premise.**

1. **The data.** By `ghb7-finite-index-z-extension-center-survives`, fix `K <= G` of finite index and
   `1 → ⟨z⟩ → K~ → K → 1` with `K~` of finite abelianization, and finite quotients `θ_k : K~ → Q_k`
   in which `z̄ = θ_k(z)` has order `n_k → ∞`.
2. **Property (T).**
   - `G` is Kazhdan (`cckw-ghb2-kms-group-structure`, item 1), so its finite-index subgroup `K` is
     Kazhdan (standard) and finitely generated.
   - `K~` is finitely generated, since `K` is and `z` is central.
   - `K~/⟨z⟩ ≅ K` is Kazhdan and `K~` has finite abelianization, so `K~` is Kazhdan
     (`bdhv-central-extension-property-t`).
3. **The models.** Let `λ_k` be the left regular representation of `Q_k`, and `ρ_k` its restriction
   to the range of `E = (1/n_k) Σ_(j<n_k) e^(−2πij/n_k) λ_k(z̄^j)`, pulled back along `θ_k`.
   - `z̄` acts freely on `Q_k`, so `rank E = |Q_k|/n_k >= 1`, and `ρ_k(z) = e^(2πi/n_k)·1`.
   - With `N = ⟨z⟩`: `||ρ_k(z^j) − 1||_2 = |e^(2πij/n_k) − 1| → 0` for every `j`, which is (KC1) of
     `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`.
   - `Fix_N(ρ_k) = 0`, because `z` acts by the scalar `e^(2πi/n_k) ≠ 1`. So `tr E_k = 0`.
4. **No rounding.** By items 1 and 2 of `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`,
   `α_k = ρ_k∘s` is an asymptotic representation of `K` with no flexibly rounding subsequence. So `K`
   is not flexibly HS stable.
5. **Up to `G`.** By item 2 of `flexible-hs-stability-descends-to-retracts-finite-index`, stability of
   the Kazhdan group `G` would make `K` stable. So `G` is not flexibly HS stable. ∎

**Scope.** Unlike `rf-kazhdan-group-not-flexibly-hs-stable`, no subgroup `Z^2` and no symmetric
cocycle test is used: the only inputs are property (T) of the central cover and the survival of its
centre.
