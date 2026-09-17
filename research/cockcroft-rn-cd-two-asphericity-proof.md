---
rg: 2
id: cockcroft-rn-cd-two-asphericity-proof
kind: route
title: Spherical cycles form a projective summand killed by the augmentation ideal, and residual nilpotence of the ideal kills it
target: cockcroft-2-complexes-over-rn-cd-two-groups-are-aspherical
requires: []
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**Notation.**
- X is a connected CW 2-complex, G = π₁(X), X̃ is the universal cover and I ⊂ ZG
  is the augmentation ideal.
- C_i = C_i(X̃) is the cellular chain group. It is a free left ZG-module with
  basis a chosen lift of each i-cell; there is no bound on the rank.
- For a left module M, Z ⊗_G M = M / IM.

1. **The chain complex.** 0 → C₂ --∂₂--> C₁ --∂₁--> C₀ --ε--> Z → 0 is exact at
   C₁, C₀ and Z, because X̃ is connected and simply connected.
   - Put Z₁ = ker ∂₁ = im ∂₂ and Z₂ = ker ∂₂.
   - There are no 3-cells, so H₂(X̃) = Z₂.
   - X̃ is simply connected, so the Hurewicz map gives π₂(X) ≅ π₂(X̃) ≅ Z₂.

2. **Z₁ is projective, and Z₂ is a direct summand of C₂.**
   - C₀ and C₁ are free, so dimension shifting along 0 → Z₁ → C₁ → C₀ → Z → 0
     gives, for every ZG-module M,
     Ext¹_{ZG}(Z₁, M) ≅ Ext²_{ZG}(ker ε, M) ≅ Ext³_{ZG}(Z, M) = H³(G; M) = 0,
     because cd G ≤ 2.
   - Hence Z₁ is projective.
   - So 0 → Z₂ → C₂ → Z₁ → 0 splits, C₂ = Z₂ ⊕ Q with Q ≅ Z₁, and applying Z ⊗_G –
     keeps it split exact:
     0 → Z ⊗_G Z₂ → Z ⊗_G C₂ → Z ⊗_G Z₁ → 0. (∗)
   - In particular Z ⊗_G Z₂ → Z ⊗_G C₂ = C₂(X) is injective.

3. **The Hurewicz map.** The covering map p: X̃ → X is cellular, and on 2-chains it is
   the quotient C₂ → Z ⊗_G C₂ = C₂(X), x ↦ 1 ⊗ x.
   - Naturality of Hurewicz gives h_X ∘ p_* = H₂(p) ∘ h_{X̃}, where p_* on π₂ and
     h_{X̃} are isomorphisms.
   - So, up to isomorphism, h_X is the composite
     Z₂ ↠ Z ⊗_G Z₂ ↪ Z ⊗_G C₂ ⊇ H₂(X).
   - The first map is onto and the second is injective by step 2. Hence the image of
     h_X is isomorphic to Z ⊗_G Z₂.
   - Therefore X is Cockcroft ⟺ Z ⊗_G Z₂ = 0 ⟺ Z₂ = I·Z₂.

4. **Residual nilpotence of I kills Z₂.** Suppose Z₂ = I·Z₂.
   - By induction Z₂ = Iᵏ·Z₂ ⊆ Iᵏ·C₂ for every k.
   - Write C₂ = ⊕_{j∈J} ZG·e_j. Since Iᵏ is a two-sided ideal and every element
     of C₂ has finite support, Iᵏ·C₂ = ⊕_j Iᵏ·e_j.
   - Membership in ⊕_j Iᵏ e_j is tested coordinatewise, so
     ⋂_k Iᵏ·C₂ = ⊕_j (⋂_k Iᵏ)·e_j = 0.
   - Hence Z₂ = 0.

5. **Conclusion.** π₂(X) = Z₂ = 0.
   - X̃ is a simply connected 2-complex with H₂ = 0, so all its homology vanishes.
   - By the Hurewicz and Whitehead theorems X̃ is contractible, so X is aspherical.
   - The converse (aspherical ⇒ Cockcroft) is trivial.

6. **When ⋂ₙ Iⁿ = 0 holds.**
   - **(a) Jennings.** S. A. Jennings, *The group ring of a class of infinite
     nilpotent groups*, Canad. J. Math. 7 (1955) 169–187, as summarised in the
     Springer reprint abstract: for a finitely generated torsion-free nilpotent
     group Q, the augmentation ideal of kQ, char k = 0, is residually nilpotent.
     Since Iⁿ(ZQ) ⊆ Iⁿ(QQ), we get ⋂ Iⁿ(ZQ) = 0.
   - **(b) Finitely generated residually torsion-free nilpotent G.**
     - Let x = Σ a_g g ≠ 0 lie in ⋂ Iⁿ(ZG), with finite support S.
     - Finitely many torsion-free nilpotent quotients separate the elements of S.
       The image of G in their product is a finitely generated torsion-free
       nilpotent quotient G/K on which S injects.
     - The map π: ZG → Z[G/K] carries Iⁿ(ZG) into Iⁿ(Z[G/K]). So π(x) is a nonzero
       element of ⋂ Iⁿ(Z[G/K]), contradicting (a).
   - **(c) Subgroups.** For H ≤ G, I(ZH) ⊆ I(ZG), so Iⁿ(ZH) ⊆ Iⁿ(ZG) and
     ⋂ Iⁿ(ZH) ⊆ ⋂ Iⁿ(ZG).
   - **(d) Right-angled Artin groups.** Finitely generated RAAGs are residually
     torsion-free nilpotent (Duchamp--Krob, *The lower central series of the free
     partially commutative group*, Semigroup Forum 45 (1992)). So every subgroup of a
     RAAG A_L satisfies hypothesis 2, in particular the Bestvina--Brady kernel
     `H_L` ≤ A_L. Hartley and Lichtman give general criteria (Lichtman, Mat.
     Sbornik 1977), but these are not needed here.

**Where each hypothesis is used.**
- cd ≤ 2 is used only in step 2.
- ⋂ Iⁿ = 0 is used only in step 4.
- Step 2 is where the 3-torus calibration fails: there Ext³ ≠ 0 and Z₁ is not
  projective.

**Verification tier.**
- Steps 1–5 are complete, self-contained module theory.
- Step 6 relies on two cited theorems. Jennings was checked only against the
  abstract of the Springer reprint; Duchamp--Krob is standard.
