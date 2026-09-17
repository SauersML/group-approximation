---
rg: 2
id: tucker-drob-sandwich-sets-open-at-free-actions
kind: claim
title: Sandwich-cost sets localize to finitely generated subgroups, are open at free actions, and characterize pseudocost
distinct_from:
  tucker-drob-pseudocost-exhaustion-bounds: that imports the pseudocost definition, Corollary 6.8 (PC = C when C is finite) and Proposition 6.26(1) (PC at least C(Gamma)); this imports Lemma 6.2 (sandwich relations localize to finitely generated subgroups), Theorem 6.4 (openness at free actions), Corollary 6.19 (PC via sandwich sets) and Corollary 6.20 (pseudocost monotonicity under weak containment).
artifacts:
  - research/artifacts/fpbs-sandwich-cost-quantifier-shift-2026-09-17.md
  - research/artifacts/fpbs/docs/fixed-price-countable-passage.md
---

**ESTABLISHED (literature import).** Let `Γ` be a countable group, `F ⊆ Γ`
finite, `r ∈ ℝ ∪ {∞}`, and `a = Γ ↷ (X, μ)` a measure-preserving action.

- **(1) Localization (Lemma 6.2, `lem:open`).** The following are equivalent:
  - there is a subequivalence relation `E` with
    `E_{a|⟨F⟩} ⊆ E ⊆ E_a` and `C_μ(E) < r`;
  - there are a finite `Q ⊇ F` and `E` with
    `E_{a|⟨F⟩} ⊆ E ⊆ E_{a|⟨Q⟩}` and `C_μ(E) < r`.

  `A_{F,r}` denotes the set of actions satisfying these conditions. It is
  isomorphism invariant.
- **(2) Openness (Theorem 6.4, `thm:KecOpen`).** If `Γ` is infinite,
  `A_{F,r} ∩ FR` is contained in the interior of `A_{F,r}`.
- **(3) Pseudocost (Corollary 6.19, `cor:PCdef`).** `PC(a) ≤ r` iff
  `a ∈ A_{F,r+ε}` for every finite `F ⊆ Γ` and every `ε > 0`.
- **(4) Monotonicity (Corollary 6.20, `cor:AFrPC`).** If `a` is free and
  `a ≼ b`, then `PC(b) ≤ PC(a)`.

Source: R. Tucker-Drob, arXiv:1211.6395. Route:
`tucker-drob-sandwich-sets-open-at-free-actions-citation`. The numbering
follows the tool table of the passage artifact, where these statements were
already used without a graph node.
