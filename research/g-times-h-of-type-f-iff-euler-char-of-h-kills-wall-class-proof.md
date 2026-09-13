---
rg: 2
id: g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class-proof
kind: route
title: "Proof of the product criterion: the Euler class of G x H is chi(H) times the induced Euler class of G"
target: g-times-h-of-type-f-iff-euler-char-of-h-kills-wall-class
requires:
  - fp-type-fp-group-is-type-f-iff-wall-class-vanishes
---

Facts (S1)–(S5) are those of
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof`. Let `Γ = G × H`, with
inclusion `i : G → Γ` and projection `r : Γ → G`, so `r ∘ i = id`. Write
`i_* : K_0(ZG) → K_0(ZΓ)` for induction and `r_* : K_0(ZΓ) → K_0(ZG)` for extension of
scalars along `r : ZΓ → ZG`. Then `r_* i_* = id`, since
`ZG ⊗_{ZΓ} ZΓ ⊗_{ZG} P = P` along `r ∘ i = id`, and `r_*[ZΓ] = [ZG]`.

**Retract step.** If `Γ` is of type F, the retract argument of
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof` ((1) ⇒ (3)) applies
verbatim with `H` in place of `Z`: `G` is finitely presented, of type `FP_∞`, with
`cd G ≤ cd Γ < ∞`, hence of type FP.

**Product resolution.** Let `G` be finitely presented of type FP with finite
projective resolution `P_*`, and let `Q_*` be a finite free resolution of `Z` over
`ZH` with `Q_j = (ZH)^{m_j}` (it exists because `H` is of type F). Then
`χ(H) = Σ_j (−1)^j m_j`. The complex `P_* ⊗_Z Q_*` is a finite resolution of `Z` over
`ZΓ = ZG ⊗_Z ZH`: the terms are free abelian, so Künneth over `Z` gives homology `Z`
in degree 0. Its terms `P_i ⊗_Z (ZH)^{m_j} ≅ (ZΓ ⊗_{ZG} P_i)^{m_j}` are finitely
generated projective. Its Euler class is

    E(Γ) = Σ_{i,j} (−1)^{i+j} m_j [ZΓ ⊗_{ZG} P_i] = χ(H) · i_* E(G),

where `E(G) = Σ_i (−1)^i [P_i]`. So `Γ` is finitely presented of type FP, and
`σ(Γ) = χ(H) · i_* σ(G)` in `K̃_0(ZΓ)`.

**(⇐).** If `χ(H) σ(G) = 0` then `σ(Γ) = 0`. By
`fp-type-fp-group-is-type-f-iff-wall-class-vanishes`, `Γ` is of type F.

**(⇒).** If `Γ` is of type F, then `G` is finitely presented of type FP by the
retract step, and `E(Γ) ∈ Z·[ZΓ]`, because `σ(Γ) = 0` and `E(Γ)` does not depend
on the resolution. Applying `r_*` gives `χ(H) · E(G) ∈ Z·[ZG]`, that is
`χ(H) · σ(G) = 0`.

**Corollaries.** If `χ(H) = ±1`, then `σ(G) = 0`, so `G` is of type F. If
`χ(H) = 0`, the condition is vacuous. For `H = Z` this recovers
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd`.

Model tests. `H = F_2`, `G = Z`: `Z × F_2` is of type F, and so is `Z`. `H = Z`, `G`
a Bestvina–Brady group that is FP but not finitely presented: `G × Z` is not
finitely presented, consistent with the retract step.

Unreviewed as of 2026-09-13: owed to z-verify-topology.
