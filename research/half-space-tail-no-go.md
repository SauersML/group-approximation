---
rg: 2
id: half-space-tail-no-go
kind: claim
title: Half-space tensor models die in the tail
invalidates: [half-space-tensor-models]
---

`centralized_mem_iterate` (formalized) plus tail triviality. If the
compressor centralizes `F ≤ Γ` then `F ≤ φⁿ(Γ)` for all `n`; for a
half-space tensor construction any `γ ∈ ⋂ₙ φⁿ(Γ)` has `ρ(γ)` in the tail
`= ℂ`, contradicting `τ(ρ(γ)) = 0`.

Scope, corrected: the half-space hypothesis is essential. Splitting off the
constants puts them on the two-sided diagonal (shift-invariant, not in the
tail) and leaves `⋂_w φ_w(Γ(𝔪)) = 1` for two compressors. This rules out
half-space towers, NOT all tensor models.
