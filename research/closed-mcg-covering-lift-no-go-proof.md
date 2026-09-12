---
rg: 2
id: closed-mcg-covering-lift-no-go-proof
kind: route
title: A covering lift would split the Birman sequence virtually, which Chen--Salter exclude from genus four on
target: closed-mcgs-have-no-covering-lift-to-marked-covers
requires:
  - outer-covering-lifts-are-virtual-sections
  - birman-exact-sequence-does-not-virtually-split
---

Suppose `L`, `π: Σ̃ → Σ`, `P` and `λ` are as in the target, with `g ≥ 4`.
1. Part (ii) of `outer-covering-lifts-are-virtual-sections` gives a section of
   `1 → π1(Σ, x) → Mod(Σ, x) → Mod(Σ) → 1` over a finite-index subgroup `L′`
   of `L`.
2. `L′` has finite index in `Mod(Σ)`, so the Birman sequence virtually splits.
3. For `g ≥ 4` this contradicts Theorem A of Chen--Salter,
   `birman-exact-sequence-does-not-virtually-split`.

Hence no such data exist. Nowhere is injectivity of `λ` used. `∎`
