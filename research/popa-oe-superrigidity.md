---
rg: 2
id: popa-oe-superrigidity
kind: claim
title: Free s-malleable weakly mixing actions of groups with property (T) and no finite normal subgroups are OE superrigid and superrigid for embeddings
distinct_from:
  popa-bernoulli-cocycle-superrigidity: that imports Theorem 0.1, cocycle superrigidity; this imports Theorems 0.3 and 0.4, orbit equivalence superrigidity and superrigidity of embeddings of orbit relations, which the paper derives from 0.1
---

**ESTABLISHED (literature import).** S. Popa, *Cocycle and orbit equivalence superrigidity
for malleable actions of w-rigid groups*, arXiv:math/0512646v8 (Invent. Math. 170 (2007)),
read from the PDF, pages 1 to 6.

**Theorem 0.1** (p. 4, hypotheses only): *"Let Γ ↷^σ X be a s-malleable action (e.g. a
generalized Bernoulli Γ-action) and assume Γ has an infinite rigid subgroup H such that
either H is wq-normal with σ mixing, or that H is w-normal with σ|H weak mixing."*

**Theorem 0.3 (OE superrigidity)** (p. 5): *"Let Γ ↷^σ X be as in 0.1. and assume in
addition that Γ has no nontrivial finite normal subgroups and σ is free. Let θ be an
arbitrary free ergodic measure preserving action of a countable discrete group Λ on a
standard probability space (Y, ν). If Δ is an isomorphism of probability spaces which takes
ℛ_σ onto ℛ_θ^t, for some t > 0, then n = t^{-1} is an integer and there exist a subgroup
Λ_0 ⊂ Λ of index [Λ : Λ_0] = n, a subset Y_0 ⊂ Y of measure ν(Y_0) = 1/n fixed by θ|Λ_0,
an inner automorphism α ∈ Inn(ℛ_θ) and a group isomorphism δ : Γ ≃ Λ_0 such that α∘Δ
takes X onto Y_0 and conjugates the actions σ, θ_0∘δ, where θ_0 denotes the action of Λ_0
on Y_0 implemented by θ."*

**Theorem 0.4 (superrigidity of embeddings)** (p. 5): *"Let Γ ↷^σ X be as in 0.1,
Λ ↷^θ Y an arbitrary free ergodic action and t > 0. If Δ : (X, μ) ≃ (Y, ν)^t is an
identification of ℛ_σ with a subequivalence relation of ℛ_θ^t such that any Γ-invariant
finite subequivalence relation of ℛ_θ^t must be contained in ℛ_σ, then t ≤ 1 and there
exists an isomorphism δ : Γ ≃ Λ_0 ⊂ Λ and α ∈ Inn(ℛ_θ) such that α∘Δ takes X onto a
Λ_0-invariant subset Y_0 ⊂ Y, with ν(Y_0) = t, and conjugates the actions σ, θ|Λ_0 with
respect to the identification δ : Γ ≃ Λ_0."*

**Generalized Bernoulli actions** (pp. 3 to 5): for `Γ` acting on a countable set `K`,
`σ_g((t_k)_k) = (t_{g^{-1}k})_k` on `Π_(k∈K)(X_0, μ_0)_k` *"is called a generalized Bernoulli
Γ-action and it is still s-malleable"*; it *"is weak mixing iff |Γk| = ∞, ∀k"*; and *"the
condition |{k ∈ K | gk ≠ k}| = ∞, ∀g ∈ Γ \ {e}, insures that σ is free."* An infinite group
with property (T) is an infinite rigid subgroup of itself (p. 3: *"Infinite property (T)
groups ... have infinite normal rigid subgroups"*).

**Trust surface.** Refereed. Statement-level import from the introduction; Definition 4.3
(s-malleability) and the proofs were not read.
