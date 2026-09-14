---
rg: 2
id: subshift-restriction-kernel-relative-elementary-proof
kind: route
title: Split off Z, kill the biasymptotic part with the locally matricial ideal, lift the Z part through I_Y, then read off the K_2 cokernel
target: subshift-restriction-kernel-is-relative-elementary
requires: [ultramatricial-ideals-have-elementary-congruence-kernels, biasymptotic-subshift-complement-ideal-is-ultramatricial]
artifacts:
  - research/artifacts/sk-k2-subsystems-2026-09-13-part1.md
---

The full proofs are Theorem D and Lemma A in the artifact.
- **Split.** Put Y′ = Y ∪ Z. Y and Z are disjoint closed sets, so R_{Y′} = R_Y × R_Z and EL_n(R_{Y′}) = EL_n(R_Y) × EL_n(R_Z).
- **The Y′ kernel.** By the two required nodes applied to Y′, ker π_{Y′} ⊆ GL_n(R_X, I_{Y′}) = E_n(I_{Y′}) ⊆ E_n(I_Y).
- **Lift the Z part.**
  - Choose a clopen U ⊇ Z with U ∩ Y = ∅. Each r ∈ R_Z lifts to I_Y: extend the coefficients and multiply them by e_U.
  - So π_{Y′}(E_n(I_Y)) ⊇ 1 × EL_n(R_Z).
  - For g ∈ ker π_Y pick h ∈ E_n(I_Y) with π_{Y′}(h) = π_{Y′}(g). Then g h^{-1} ∈ ker π_{Y′} ⊆ E_n(I_Y).
- **Lemma A.** St_n(R/I) = St_n(R)/⟨⟨x_ij(I)⟩⟩, and ⟨⟨x_ij(I)⟩⟩ maps onto E_n(R,I). Lifting g ∈ EL_n(R) ∩ GL_n(R,I) to St_n(R) and reducing mod I gives a well-defined homomorphism onto coker(K_2(n,R) → K_2(n,R/I)) with kernel E_n(R,I).
- So the kernel equality gives surjectivity of K_2(n,R_X) → K_2(n,R_Y). ∎
