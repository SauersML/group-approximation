---
rg: 2
id: contractible-complex-minus-cell-homology-proof
kind: route
title: Cell count and the long exact sequence of the pair (L, K)
target: contractible-complex-minus-cell-has-cyclic-homology
requires: []
artifacts:
  - research/artifacts/ideas-topology-2026-09-14.md
---

Notation as in the claim: L finite contractible 2-complex, e an open 2-cell, K = L − e.

1. **Connectedness.** K contains the 1-skeleton of L, which is connected.
2. **Euler characteristic.** χ(L) = 1 because L is contractible, and K has one
   2-cell fewer, so χ(K) = 0.
3. **Relative homology.** The cellular chain complex of (L, K) is Z in degree 2
   and zero elsewhere, so H₂(L, K) ≅ Z and H_i(L, K) = 0 for i ≠ 2.
4. **Long exact sequence.** From
   H₃(L,K) → H₂(K) → H₂(L) → H₂(L,K) → H₁(K) → H₁(L) with H₃(L,K) = 0 and
   H₂(L) = H₁(L) = 0, we get H₂(K) = 0 and H₁(K) ≅ H₂(L,K) ≅ Z.
5. **Weight one.** By van Kampen, π₁(L) = π₁(K)/⟨⟨γ⟩⟩, where γ is the attaching loop
   of e. π₁(L) = 1, so γ normally generates π₁(K).
6. **Infinite.** π₁(K) surjects onto H₁(K) ≅ Z.

Elementary; no imports.
