---
rg: 2
id: genus-three-covering-lift-no-go-proof
kind: route
title: A covering lift in genus three would split the genus-three Birman sequence virtually
target: genus-three-mcg-has-no-covering-lift-to-marked-covers
requires:
  - outer-covering-lifts-are-virtual-sections
  - birman-sequence-genus-three-does-not-virtually-split
---

Suppose `L`, `π: Σ̃ → Σ`, `P` and `λ` are as in the target, with `g = 3`.
1. By part (ii) of `outer-covering-lifts-are-virtual-sections`, the sequence
   `1 → π1(Σ, x) → Mod(Σ, x) → Mod(Σ) → 1` has a section over a finite-index
   subgroup `L′` of `L`.
2. `L′` has finite index in `Mod(Σ)`, so the genus-three Birman sequence virtually
   splits.
3. That contradicts `birman-sequence-genus-three-does-not-virtually-split`.

So no such data exist. Injectivity of `λ` is never used. `∎`
