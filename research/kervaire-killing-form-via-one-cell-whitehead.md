---
rg: 2
id: kervaire-killing-form-via-one-cell-whitehead
kind: route
title: Whitehead's finite one-cell case already forbids balanced Kervaire killing failures, via the wedge retraction
target: kervaire-killing-form-holds-over-nonnegative-deficiency-groups
requires:
  - contractible-2-complex-minus-a-cell-is-aspherical
  - deficiency-zero-kervaire-failure-yields-whitehead-counterexample
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

Let G ≠ 1 have a finite presentation ⟨x₁, …, xₙ | r₁, …, r_m⟩ with m ≤ n and presentation
complex K. Let w ∈ G * ⟨t⟩, and write G_w = (G * ⟨t⟩)/⟨⟨w⟩⟩.

- **If m < n:** item 1 of `deficiency-zero-kervaire-failure-yields-whitehead-counterexample`
  makes G_w infinite.
- **If m = n and G_w = 1:** item 2(b) of the same theorem gives a finite contractible
  2-complex L, the presentation complex of ⟨x₁, …, xₙ, t | r₁, …, rₙ, W⟩ for a word W
  representing w. Item 2(c) gives π₂(K) ≠ 0.
  1. Let e_W be the 2-cell of L attached along W. Then L − e_W has one 0-cell, the 1-cells
     x₁, …, xₙ, t and the 2-cells r₁, …, rₙ. It is the wedge K ∨ S¹, where the circle is t.
  2. Collapsing the circle gives a retraction ρ: K ∨ S¹ → K with ρ restricted to K equal
     to the identity. So π₂(K) → π₂(K ∨ S¹) is split injective, and π₂(L − e_W) ≠ 0.
  3. This contradicts `contractible-2-complex-minus-a-cell-is-aspherical`.

So G_w ≠ 1 in both cases.

**Comparison.** `nonnegative-deficiency-kervaire-via-finite-whitehead` reaches the same
target from the full `whitehead-asphericity-conjecture`. This route needs only
complements of a single 2-cell.
