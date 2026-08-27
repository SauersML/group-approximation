---
rg: 2
id: defect-forces-proper-self-embedding-proof
kind: route
title: Conjugate the commutation relation by the stable letter
target: defect-forces-proper-self-embedding
requires: []
artifacts:
  - GroupApproximation/Sofic/ConcreteCompressionSource.lean
---

## Complete argument

For every `γ ∈ Γ`, `[c, ι(γ)] = 1`.  Conjugating by `t`:
`[t c t⁻¹, t ι(γ) t⁻¹] = 1`, i.e. `[t c t⁻¹, ι(α γ)] = 1`.  If `α` is
surjective this says `t c t⁻¹` commutes with all of `ι(Γ)`, so every
normal generator `[t c t⁻¹, ι(γ)]` of the defect is trivial and
`N = ⊥`.  Contrapositive: `N ≠ ⊥ ⟹ α(Γ) ⊊ Γ`.

For corollary 1: the transported mark commutes with `ι(α(Γ))` by the
displayed identity, and a co-Hopfian `Γ` has no proper self-embedding at
all, so no core over it has a nontrivial defect.  The linear-centralizer
remark is the standard computation that a matrix commuting with all
elementary congruence matrices `1 + m E_{ij}` is scalar.  Corollary 2 is
a reading of which fields the kernel-checked chain
`DefectRoutingData → full MF radical → non-MF` actually consumes: the
normal-Kazhdan obstruction is invoked at the whole routed quotient,
whose (T) comes from `RoutingLemmaData.kazhdan` — the partner surjection
— never from the core's own (T) field.  The W0 interface wave is
verifying that consumer trace mechanically in Lean.
