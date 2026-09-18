---
rg: 2
id: fpbs-pseudocost-localizes-to-fg-sandwich-costs
kind: claim
title: Pseudocost is a sup over finite sets of an inf over finitely generated subgroups of sandwich costs, and Bernoulli shifts restrict to Bernoulli shifts
distinct_from:
  tucker-drob-sandwich-sets-open-at-free-actions: that is the imported equivalence of sandwich conditions for one finite set and one action; this assembles it into the formula PC(a) = sup_F inf_Delta p^Delta_F(a|Delta) over finitely generated subgroups, adds the isomorphism s_Gamma|Delta = s_Delta, and gives PC(s_Gamma) in terms of finitely generated subgroups only.
  tucker-drob-pseudocost-exhaustion-bounds: that bounds pseudocost by costs along exhaustions and from below by C(Gamma); this is an exact formula for pseudocost through relative sandwich costs of finitely generated subgroups.
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
  - research/artifacts/fpbs/docs/fixed-price-countable-passage.md
---

**ESTABLISHED.** For a countable group `Δ`, a p.m.p. action `a` of `Δ` and a
finite `F ⊆ Δ`, define the sandwich cost

    p^Δ_F(a) = inf { C(E) : E_{a|⟨F⟩} ⊆ E ⊆ E_a } ∈ [0, ∞].

Let `s_Δ` be the Bernoulli shift `[0,1]^Δ`. Let `Γ` be a countable group, `a` a
p.m.p. action of `Γ`, and `F ⊆ Γ` finite.

1. **Localization.**
   `p^Γ_F(a) = inf { p^Δ_F(a|Δ) : Δ ≤ Γ finitely generated, F ⊆ Δ }`. The
   quantity `p^Δ_F(a|Δ)` is nonincreasing in `Δ`.
2. **Pseudocost.** `PC(a) = sup_F p^Γ_F(a)`. So
   `PC(a) = sup_F inf_{Δ f.g., F ⊆ Δ} p^Δ_F(a|Δ)`.
3. **Bernoulli restriction.** For every subgroup `Δ ≤ Γ`, `s_Γ|Δ ≅ s_Δ`.
   Hence
   `PC(s_Γ) = sup_F inf_{Δ f.g., F ⊆ Δ} p^Δ_F(s_Δ)`.
4. **Freeness.** If `Γ` is infinite, `s_Γ` is essentially free.

The pseudocost of the Bernoulli shift of any countable group is therefore
determined by the relative sandwich costs of Bernoulli shifts of its finitely
generated subgroups.

Route: `fpbs-pseudocost-localizes-to-fg-sandwich-costs-proof`.
