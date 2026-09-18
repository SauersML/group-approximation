---
rg: 2
id: fg-groups-have-fg-derivative-images-proof
kind: route
title: Induct on word length with the cocycle identity
target: fg-groups-have-fg-derivative-images
requires: []
---

**1. Identity and inverses.** Putting `γ = δ = 1` in the cocycle identity gives
`c(1, x) = c(1, x)^2`, so `c(1, x) = 1`. Putting `γ = s^-1`, `δ = s` and
replacing `x` by `s^-1 x` gives `1 = c(s^-1, x) · c(s, s^-1 x)`. So
`c(s^-1, x) = c(s, s^-1 x)^-1 in Λ`.

**2. Words.** Let `γ = s_1^{e_1} ... s_k^{e_k}` with `s_i in S` and
`e_i = ±1`, and write `γ = σ γ'` with `σ = s_1^{e_1}`. The cocycle identity
gives `c(γ, x) = c(σ, γ' x) · c(γ', x)`. The first factor is in `Λ` by step 1,
and the second is in `Λ` by induction on `k`. This proves part 1. `Λ` is
finitely generated because each `c(s, -)` takes finitely many values.

**3. Stabilizers.** For `γ, δ in Γ_x` we have `δ x = x`, so
`c(γδ, x) = c(γ, x) c(δ, x)`. This proves part 2.
