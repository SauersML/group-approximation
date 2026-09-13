---
rg: 2
id: dead-vertex-raag-kernels-retract-onto-subgraph-kernels
kind: claim
title: A RAAG kernel whose character vanishes off an induced subgraph retracts onto the kernel of the restricted character
---

Let `Λ ⊆ Γ` be an induced subgraph and `χ : A_Γ → Z` a homomorphism with
`χ(v) = 0` for every vertex `v ∉ Λ`. Write `χ_Λ = χ|_{A_Λ}`. Then `ker χ_Λ`
is a retract of `ker χ`. So if `ker χ` is finitely presented, then `ker χ_Λ`
is finitely presented and `δ_{ker χ_Λ} ≼ δ_{ker χ}`.

Use: Dehn functions of kernels with dead vertices dominate the kernels on the
living subgraph (take `Λ` = the living subgraph). The other direction fails in
general: in `raag-kernel-dehn-function-below-bestvina-brady` the kernel on the
living path is free.

Established by `dead-vertex-raag-kernels-retract-onto-subgraph-kernels-proof`,
unreviewed as of 2026-09-13.
