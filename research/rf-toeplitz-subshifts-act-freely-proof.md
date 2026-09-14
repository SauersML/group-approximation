---
rg: 2
id: rf-toeplitz-subshifts-act-freely-proof
kind: route
title: Limits along translates with a fixed residue keep one non-constant coset per level, and stabilizing all of them forces the identity
target: rf-toeplitz-subshifts-act-freely
requires: [rf-toeplitz-subshifts-over-residually-finite-groups]
artifacts:
  - research/artifacts/sk-universal-embedding-a-rf-embedding-2026-09-13.md
---

Artifact §3, Lemma 3. Convention `(g·y)(h) = y(g^(-1)h)`.

1. **The array.**
   - (F1) `x` is constant on every coset of `Γ_m` except the hole `C_m`.
   - (F2) Inside `C_m`, `x ≡ 1` on one coset of `Γ_(m+1)` and `x ≡ 0` on another.
   - So `g·x` is constant off `gC_m` and not constant on `gC_m`.
2. **Limits.**
   - Let `y = lim g_k·x`. Since `Γ/Γ_(m+1)` is finite, some residue `g_kΓ_(m+1)` repeats along a subsequence.
   - There `D = g_kC_m` is fixed, and so are the two cosets `E_1, E_0 ⊆ D` of `Γ_(m+1)` on which `g_k·x` is `1`,
     resp. `0`.
   - Pointwise limits preserve these equalities. So `y` is constant on every coset of `Γ_m` other than `D`, and
     `y|_(E_1) ≡ 1`, `y|_(E_0) ≡ 0`. Hence `D_m(y) := D` is the unique non-constant coset.
3. **Nesting and equivariance.**
   - A coset of `Γ_(m+1)` inside a constant coset of `Γ_m` is constant, so `D_(m+1)(y) ⊆ D_m(y)`.
   - `D_m(g·y) = gD_m(y)` because `g·y` transports constancy.
4. **Freeness.** If `g·y = y`, then `gD_m(y) = D_m(y)`. Writing `D_m(y) = cΓ_m`, this means `c^(-1)gc ∈ Γ_m`, i.e.
   `g ∈ Γ_m` by normality, for every `m`. So `g ∈ ∩ Γ_m = {e}`. ∎
