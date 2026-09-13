---
rg: 2
id: ioana-profinite-cocycle-superrigidity
kind: claim
title: Cocycles of free ergodic profinite actions of property (T) groups into countable groups come from a finite quotient
distinct_from:
  popa-bernoulli-cocycle-superrigidity: that is Popa's theorem for s-malleable actions such as Bernoulli shifts, where cocycles untwist to homomorphisms; this is Ioana's theorem for profinite actions, where cocycles untwist only to cocycles of a finite quotient
---

**ESTABLISHED by citation.** Let `Γ` be a countable group with an infinite normal subgroup `Γ_0` such that
`Γ_0 ⊂ Γ` has relative property (T) and `Γ/Γ_0` is finitely generated. Let `Γ ↷ X` be a free ergodic
measure-preserving profinite action, the inverse limit of actions on finite probability spaces `X_n` with
quotient maps `r_n : X → X_n`, and assume `Γ_0 ↷ X` is ergodic. Then for every countable group `Λ` and
every measurable cocycle `w : Γ × X → Λ` there are `n` and a cocycle `w'' : Γ × X_n → Λ` such that `w` is
cohomologous to `w''∘(id × r_n)`.

The case used here: `Γ = Γ_0` an infinite group with property (T), for instance `SL_3(Z)`, and any free
ergodic profinite action, such as the action on the profinite completion.

Consequence at a finite level. `X_n` is finite and ergodic, so `Γ` acts transitively on it. For `a ∈ X_n`
with stabilizer `Γ_a`, the map `δ ↦ w''(δ, a)` is a homomorphism `Γ_a → Λ` on a finite-index subgroup.
So every `Λ`-cocycle of the action is virtually cohomologous to a homomorphism on a finite-index subgroup,
restricted to a piece `r_n^(−1)(a)`.

Source: A. Ioana, *Cocycle superrigidity for profinite actions of property (T) groups*, arXiv:0805.2998,
Theorem B together with the hypotheses of Theorem A. Citation route
`ioana-profinite-cocycle-superrigidity-citation`.
