---
rg: 2
id: stable-finite-actions-sofic-actions-weakly-finite-proof
kind: route
title: Lift a Paunescu embedding to a sofic approximation with exact limit statistics and apply stability
target: stable-finite-actions-sofic-actions-weakly-finite
requires: []
artifacts:
  - research/artifacts/f2xf2-finite-action-stability-dichotomy-2026-09-16.md
---

Direct proof, artifact §2–§3. Fix a unital, trace-preserving embedding
`Θ : L^∞(X) ⋊ Γ → Π_ω M_{n_k}` with `L^∞(X) → Π_ω D_{n_k}` and `u_g → Π_ω P_{n_k}`.

1. **Lemma 1 (sets).** Every `Θ(1_E)` is represented by indicators `1_{A_k}`. Truncate a self-adjoint
   diagonal representative to `[0, 1]` and threshold at `1/2`. The pointwise bound
   `|1_{A_k} − a_k| ≤ 2(a_k − a_k²)` controls the error.
2. **Lemma 2 (group elements).** Permutation representatives `σ_k(g)` are asymptotically multiplicative,
   because `‖P_σ − P_{σ'}‖_2² = 2 d_H(σ, σ')`. They are asymptotically free, because
   `lim_ω |Fix σ_k(g)| / n_k = τ(u_g) = 0` for `g ≠ 1`.
3. **Lemma 3 (statistics).** `μ(E ∩ gE') = lim_ω |A_k ∩ σ_k(g) A'_k| / n_k`, by trace preservation applied
   to `1_E u_g 1_{E'} u_g*`.
4. **Lemma 4 (sizes).** `{k : n_k ≥ m} ∈ ω`. Otherwise `Γ` embeds in a finite symmetric group.
5. **Diagonal choice.** For a dense sequence `E_i` and an enumeration `g_a`, pick `k_m` in the `ω`-large set
   where every defect and statistics error indexed by `≤ m` is `< 1/m`. Then `τ_m = σ_{k_m}` is a sofic
   approximation, and its limit action `P` has internal sets `Ê_i` with
   `μ_ν(Ê_i ∩ g_a Ê_j) = μ(E_i ∩ g_a E_j)`.
6. **Conclusion.** By density `a ≺ P`, by stability `P ≺ F(Γ)`, and by transitivity `a ≺ F(Γ)`.
7. **Part 3.** Residual finiteness makes `Γ ↷ Γ̂` free with nonatomic Haar measure. When `Γ` is
   finitely generated, it has countably many finite-index subgroups, so `Γ̂` is metrizable. Otherwise,
   enumerate `Γ ∖ {1}` as `γ_i`, choose finite-index normal `N'_{γ_i} ∌ γ_i`, and use
   `K = lim Γ/(N'_{γ_1} ∩ … ∩ N'_{γ_i})` instead. The projection
   `a × Γ̂ → a` is a factor map, so `a × Γ̂ ≺ F(Γ)` would force `a ≺ F(Γ)`.
