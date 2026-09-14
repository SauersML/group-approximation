---
rg: 2
id: lot-complexes-vanishing-l2-betti-aspherical-proof
kind: route
title: Killing one vertex generator propagates along the tree, then the one-cell L² constraint applies
target: lot-complexes-with-vanishing-first-l2-betti-are-aspherical
requires:
  - whitehead-one-cell-counterexamples-have-positive-first-l2-betti
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

Notation as in the claim. L is K(Γ) with one extra 2-cell e₀ attached along the loop x₁.

1. **π₁(L) is trivial.** π₁(L) = ⟨ V | ι(e)λ(e)τ(e)⁻¹λ(e)⁻¹ (e an edge), x₁ ⟩.
   - The relator of an edge e says τ(e) = λ(e)⁻¹ ι(e) λ(e), so ι(e) = 1 in π₁(L) if and
     only if τ(e) = 1.
   - x₁ = 1, and Γ is connected, so every generator is trivial by induction on the tree
     distance from x₁.
2. **L is contractible.**
   - L has one 0-cell, n 1-cells and n 2-cells, so χ(L) = 1.
   - H₁(L) = 0 because π₁(L) = 1.
   - H₂(L) is the kernel of the cellular boundary Zⁿ → Zⁿ, so it is free abelian.
     Its rank is χ(L) − rank H₀(L) + rank H₁(L) = 0, so H₂(L) = 0.
   - L is simply connected with vanishing reduced homology, so it is contractible by
     Hurewicz and Whitehead. This proves item 1 of the claim, with K(Γ) = L − e₀.
3. **Asphericity.** Assume b₁^(2)(G(Γ)) = 0, and note G(Γ) = π₁(K(Γ)). If K(Γ) were not
   aspherical, `whitehead-one-cell-counterexamples-have-positive-first-l2-betti` applied to
   K(Γ) = L − e₀ would give b₁^(2)(G(Γ)) > 0. So K(Γ) is aspherical, which is item 2.

Elementary beyond the required claim.
