---
rg: 2
id: lot-complexes-with-vanishing-first-l2-betti-are-aspherical
kind: claim
title: Every labelled oriented tree complex is a one-cell complement of a contractible 2-complex, and it is aspherical when its group has vanishing first L²-Betti number
distinct_from:
  contractible-complex-minus-cell-has-cyclic-homology: that computes the homology of an arbitrary one-cell complement; this shows that LOT complexes are one-cell complements and draws the asphericity consequence.
  whitehead-one-cell-counterexamples-have-positive-first-l2-betti: that is about arbitrary one-cell complements; this is the LOT special case, together with the contractible augmentation.
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

**ESTABLISHED** through `lot-complexes-vanishing-l2-betti-aspherical-proof`.

A **labelled oriented tree** (LOT) Γ is a finite tree with vertex set V = {x₁, …, xₙ},
n ≥ 1, in which every edge e is oriented from ι(e) to τ(e) and carries a label
λ(e) ∈ V. Its group has the presentation

  G(Γ) = ⟨ V | ι(e) λ(e) τ(e)⁻¹ λ(e)⁻¹  (e an edge of Γ) ⟩,

and K(Γ) is the presentation 2-complex: one 0-cell, n 1-cells and n − 1 2-cells.

1. Attaching one 2-cell along x₁ turns K(Γ) into a contractible 2-complex. So K(Γ) is
   a one-cell complement in the sense of `contractible-complex-minus-cell-has-cyclic-homology`.
2. If b₁^(2)(G(Γ)) = 0, then K(Γ) is aspherical.
