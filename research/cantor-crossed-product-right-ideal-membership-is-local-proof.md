---
rg: 2
id: cantor-crossed-product-right-ideal-membership-is-local-proof
kind: route
title: Columns with local preimages give a pattern-equivariant banded quotient, by choosing preimages per window type and using compactness for the radius
target: cantor-crossed-product-right-ideal-membership-is-local
requires: []
artifacts:
  - research/artifacts/sk-exchange-2026-09-14-part1.md
---

Notation: `a = Σ_{|j|≤w}f_ju^j` acts on `V_ξ` by `aδ_n = Σ_jf_j(T^{n+j}ξ)δ_{n+j}`, so `a(m,n) = f_{m−n}(T^mξ)`. The representations `V_ξ` together are faithful; one dense orbit already suffices.

**Covariance.** The map `δ_{t+s} ↦ δ_s` from `V_ξ` to `V_{T^tξ}` intertwines every element of `R`. So a statement about the column `t` at `ξ` is the same statement about the column `0` at `T^tξ`.

**(1 ⇒ 2).** If `z = ar` and `r` has propagation `w_r`, then `zδ_t = a(rδ_t)` with `rδ_t ∈ span{δ_s : |s−t| ≤ w_r}`. Take `ρ = w_r`.

**(2 ⇒ 3).** Immediate.

**(3 ⇒ 2).**
- For `ρ ≥ 0` let `G_ρ ⊆ X` be the set of `ξ` such that `zδ_0 ∈ a·span{δ_s : |s| ≤ ρ}` in `V_ξ`.
- This is a finite linear system. Its coefficients are the values `f_j(T^mξ)` for `|m| ≤ ρ+w`, and its right side the values `ζ_m(T^mξ)` (`z = Σζ_ju^j`, `|m| ≤ w_z`). These are locally constant in `ξ`, so `G_ρ` is a union of atoms of a finite clopen partition, hence clopen.
- `G_ρ` increases with `ρ`, and by (3) the `G_ρ` cover `X`. By compactness `G_ρ = X` for some `ρ`, and covariance gives (2) at every `t`.

**(2 ⇒ 1).**
1. **Window types.** Let `𝒬` be the finite clopen partition of `X` such that on each atom `Q` all values `f_j(T^mξ)` (`|m| ≤ ρ+w`) and `ζ_m(T^mξ)` (`|m| ≤ w_z`) are constant.
2. **One preimage per type.** For each `Q ∈ 𝒬` the system `a v = zδ_0`, `supp v ⊆ [−ρ,ρ]`, is the same for all `ξ ∈ Q` and has a solution by (2). Fix one, `v^Q = Σ_{|n|≤ρ}c^Q_nδ_n`.
3. **The quotient.** Put `η_n = Σ_Qc^Q_n1_Q ∈ LC(X,F)` for `|n| ≤ ρ`, and `r := Σ_{|n|≤ρ}(η_n∘T^{−n})u^n ∈ R`. In `V_ξ` its entries are `r(t+n,t) = (η_n∘T^{−n})(T^{t+n}ξ) = η_n(T^tξ)`. So `rδ_t = Σ_nη_n(T^tξ)δ_{t+n}`, which is the chosen preimage `v^Q` for the atom `Q ∋ T^tξ`, translated to position `t`.
4. **Conclusion.** By covariance, `a(rδ_t)` is the translate of `a v^Q = zδ_0` at `T^tξ`, that is `zδ_t`. So `ar` and `z` agree on every `δ_t` in every `V_ξ`, and by faithfulness `z = ar ∈ aR`. ∎

**Model tests.**
- Outside the hypotheses, the proof uses only covariance and faithfulness, so it runs for the one-point system (`T = id`, `R = F[u^{±1}]`).
  - With `a = 1−u` and `z = 1−u^N`, the column `zδ_0` has the preimage `Σ_{0≤k<N}δ_k`, and indeed `z ∈ aR`.
  - With `z = 1`, `δ_0` has no finitely supported `(1−u)`-preimage, since `(1−u)v` has coefficient sum `0`. So (3) fails, and indeed `1 ∉ (1−u)R`.
- Laurent `q`: the division bound of `laurent-right-ideals-of-cantor-crossed-products-columnwise` gives `ρ = w`, recovering that lemma.
