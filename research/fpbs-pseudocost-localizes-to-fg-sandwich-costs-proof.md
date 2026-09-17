---
rg: 2
id: fpbs-pseudocost-localizes-to-fg-sandwich-costs-proof
kind: route
title: Localize sandwich relations with Lemma 6.2, read pseudocost off Corollary 6.19, and regroup Bernoulli coordinates along cosets
target: fpbs-pseudocost-localizes-to-fg-sandwich-costs
requires:
  - tucker-drob-sandwich-sets-open-at-free-actions
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
---

Direct proof (artifact §2, Lemmas 2.1–2.3). All numbered items come from
`tucker-drob-sandwich-sets-open-at-free-actions`.

1. **Localization.** Note `E_{(a|Δ)|⟨F⟩} = E_{a|⟨F⟩}`, and `F ⊆ Δ ≤ Δ'`
   gives `E_{a|Δ} ⊆ E_{a|Δ'} ⊆ E_a`.
   - (≤) and monotonicity: a relation sandwiched between `E_{a|⟨F⟩}` and
     `E_{a|Δ}` is sandwiched between `E_{a|⟨F⟩}` and `E_{a|Δ'}`, and between
     `E_{a|⟨F⟩}` and `E_a`.
   - (≥): suppose `p^Γ_F(a) < r`. Some `E` with `E_{a|⟨F⟩} ⊆ E ⊆ E_a` has
     `C(E) < r`. By item (1), (first)⇒(second), there are a finite `Q ⊇ F`
     and `E'` with `E_{a|⟨F⟩} ⊆ E' ⊆ E_{a|⟨Q⟩}` and `C(E') < r`. So
     `p^{⟨Q⟩}_F(a|⟨Q⟩) < r`.
   - If `p^Γ_F(a) = ∞`, (≤) already gives equality.
2. **Pseudocost.** By the definition of `A_{F,r}`, `a ∈ A_{F,s}` iff
   `p^Γ_F(a) < s`. Item (3) says `PC(a) ≤ r` iff `p^Γ_F(a) < r + ε` for all
   finite `F` and `ε > 0`, that is, iff `sup_F p^Γ_F(a) ≤ r`. This holds for
   every real `r`, so `PC(a) = sup_F p^Γ_F(a)` in `[0, ∞]`. Combine with step 1.
3. **Bernoulli restriction.** Choose a transversal `T` with `Γ = ⊔_{t∈T} Δt`.
   The map `Φ(x)(δ) = (x(δt))_{t∈T}` is a measure-preserving bijection
   `[0,1]^Γ → ([0,1]^T)^Δ`. It is `Δ`-equivariant for the shifts
   `(δ·x)(η) = x(δ^{-1}η)`, since
   `Φ(δ_0·x)(δ) = (x(δ_0^{-1}δt))_t = (δ_0·Φ(x))(δ)`.
   - The base `([0,1]^T, λ^{⊗T})` is standard and nonatomic, so a measure
     isomorphism `θ` onto `([0,1], λ)` exists. Applied coordinatewise, it
     gives `([0,1]^T)^Δ ≅ s_Δ` equivariantly.
   - An isomorphism of actions carries `E_{a|⟨F⟩}`, `E_a`, sandwiched
     relations and costs to the corresponding objects. So `p^Δ_F` is an
     isomorphism invariant, matching the isomorphism invariance of `A_{F,r}`
     in item (1).
   - So `p^Δ_F(s_Γ|Δ) = p^Δ_F(s_Δ)`, and step 2 gives the formula for
     `PC(s_Γ)`.
4. **Freeness.** For `γ ≠ e` and any `η`, `γ^{-1}η ≠ η`. A point fixed by `γ`
   has `x(γ^{-1}η) = x(η)`, an event of measure 0 for independent uniform
   coordinates. The union over the countably many `γ ≠ e` is null.
