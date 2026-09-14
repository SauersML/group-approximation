---
rg: 2
id: lef-groups-lie-in-derived-subgroups-of-infinite-lef-groups-proof
kind: route
title: Constant functions in Q wr Z/m are commutators of power sequences with the shift, so an ultraproduct puts a LEF group in a derived subgroup
target: lef-groups-lie-in-derived-subgroups-of-infinite-lef-groups
requires: []
artifacts:
  - research/artifacts/sk-lef-proof-compress-proposal-2026-09-13.md
---

Complete derivation. The convention is `[g,h] = g h g^(-1) h^(-1)`.

1. **Ultraproduct copy.**
   - Let `φ_n : B_n → Q_n` be finite models of `Γ = ⟨S⟩`: injective on the ball `B_n`, with `φ_n(gh) = φ_n(g)φ_n(h)`
     whenever `g, h, gh ∈ B_n`. Extend them arbitrarily to `Γ`.
   - For a nonprincipal ultrafilter `ω`, `ι(γ) = (φ_n(γ))_n` is a homomorphism `Γ → ∏_ω Q_n` (algebraic
     ultraproduct), since `γ, δ, γδ ∈ B_n` for large `n`.
   - It is injective: `φ_n(e) = e` and injectivity on `B_n` give `φ_n(γ) ≠ e` for `γ ≠ e` and large `n`.
2. **Wreath products.**
   - Let `m_n = n|Q_n|` and `Λ_n = Q_n^(Z/m_n) ⋊ Z/m_n`, with `(t f t^(-1))(i) = f(i-1)`.
   - The constant functions `c_q` form a subgroup isomorphic to `Q_n`, so `(q_n)_n ↦ (c_(q_n))_n` embeds
     `∏_ω Q_n` in `∏_ω Λ_n`.
3. **The commutator.**
   - For `q ∈ Q_n` put `f_q(i) = q^i`. It is well defined on `Z/m_n`, as `q^(|Q_n|) = e` and `|Q_n|` divides `m_n`.
   - Then `(t f_q^(-1) t^(-1))(i) = f_q(i-1)^(-1) = q^(-(i-1))`, so `[f_q, t](i) = q^i q^(-(i-1)) = q`, and
     `[f_q, t] = c_q`.
4. **The overgroup.**
   - In `∏_ω Λ_n` put `t = (t)_n` and `f_s = (f_(φ_n(s)))_n` for `s ∈ S`. Then the copy of `ι(s)` equals `[f_s, t]`.
   - Put `Δ = ⟨t, f_s : s ∈ S⟩`. Its commutator subgroup contains the `[f_s, t]`, which generate the copy of `Γ`, so
     `Γ ↪ [Δ,Δ]`.
5. **Infinite.** For `k ≠ 0`, `t^k ≠ e` in `Λ_n` once `m_n > |k|`, which holds for all large `n`. So `t` has infinite
   order.
6. **LEF.** `Δ` is a countable subgroup of an algebraic ultraproduct of finite groups. For a finite `F ⊆ Δ`, fix
   representatives. For `ω`-almost all `n` they are injective on `F` and multiplicative on the pairs whose product lies
   in `F`, so they give finite models.

**Model tests.**
- `Γ = 1`: `Δ = ⟨t⟩ ≅ Z`, and the statement is true.
- `Γ = Z` with models `Z/k_n`: `Γ` lies in no derived subgroup of itself, but it does lie in `[Δ,Δ]` through
  `c_q = [f_q, t]`. The step is not vacuous.
- If `t` had bounded order (`m_n = |Q_n|` with `Q_n` bounded), `Δ` could be finite. The choice `m_n → ∞` is what
  makes `Δ` infinite.
