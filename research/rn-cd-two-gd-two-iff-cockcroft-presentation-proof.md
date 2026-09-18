---
rg: 2
id: rn-cd-two-gd-two-iff-cockcroft-presentation-proof
kind: route
title: Collapse a maximal tree, identify the Hurewicz image with the kernel of relators into N/[F,N], and apply the residually nilpotent asphericity criterion
target: rn-cd-two-group-has-gd-two-iff-cockcroft-presentation
requires:
  - cockcroft-2-complexes-over-rn-cd-two-groups-are-aspherical
artifacts:
  - research/artifacts/hl-whitehead-bestvina-brady-2026-09-13.md
---

**Setup.** G is a group with cd G = 2 and ⋂ Iⁿ(ZG) = 0. "Theorem A" below means
`cockcroft-2-complexes-over-rn-cd-two-groups-are-aspherical`. Steps 1–3 of its
proof use only cd G ≤ 2.

1. **(i) ⇒ (ii).**
   - If gd G = 2, there is an aspherical 2-complex X with π₁X = G.
   - π₂X = 0, so the Hurewicz map is zero and X is Cockcroft.

2. **(ii) ⇒ (i).** This is Theorem A: a Cockcroft X with π₁X = G is aspherical, so
   it is a 2-dimensional K(G,1). Also gd G ≥ cd G = 2.

3. **Presentations.** Let X be a connected 2-complex and T a maximal tree in its
   1-skeleton.
   - The quotient X → X/T is a homotopy equivalence. It is a map over the
     identity of H₂, because T carries no 2-chains, so it preserves the Cockcroft
     property in both directions.
   - X/T is the presentation complex K of ⟨S | R⟩: S is the set of 1-cells outside
     T and R the set of 2-cells, which normally generate N.
   - Conversely every presentation complex is such an X. So (ii) holds iff some
     presentation complex K of G is Cockcroft.

4. **The Hurewicz image of a presentation complex.** Let G = F(S)/N and let K be
   the complex of ⟨S | R⟩, with C_* = C_*(K̃).
   - **The relation module.** The 1-skeleton of K̃ is the Cayley graph of (G,S). It
     is the covering of the rose ⋁_S S¹ with fundamental group N, so
     Z₁ = ker ∂₁ = H₁(Cayley graph) ≅ N/[N,N].
     - F acts through G by conjugation.
     - ∂₂ sends the 2-cell e_r to the class of r. This is Lyndon's relation
       module identification; in Fox-calculus coordinates ∂₂e_r = (∂r/∂s)_s.
   - **Coinvariants.** Z ⊗_G N/[N,N] = N/[N,N] modulo the span of the elements
     f n f⁻¹ n⁻¹, which is N/[F,N].
   - **Exactness.** By step 2 of Theorem A (cd G ≤ 2), the sequence
     0 → Z ⊗_G Z₂ → Z ⊗_G C₂ = Z^(R) → Z ⊗_G Z₁ = N/[F,N] → 0 is exact. The last
     map sends e_r ↦ r[F,N].
   - **The kernel.** Hence ker(Z^(R) → N/[F,N]) ≅ Z ⊗_G Z₂.
   - **The criterion.** By step 3 of Theorem A, K is Cockcroft iff Z ⊗_G Z₂ = 0,
     that is, iff the images of R in N/[F,N] are Z-linearly independent.
   - **Spanning.** R normally generates N, and every conjugate f r f⁻¹ is congruent to
     r modulo [F,N]. So the images of R span N/[F,N], and independent images form a
     Z-basis.
   - This proves (ii) ⟺ (iii), given step 3.

5. **(ii) ⟺ (iv).**
   - Let K ⊆ X be a subcomplex of a 2-complex. H₂ of a 2-complex is the group of
     2-cycles, so H₂(K) → H₂(X) is injective. By naturality, h_X ∘ i_* = i_* ∘ h_K.
     So if X is Cockcroft, so is K. This gives (ii) ⇒ (iv).
   - Conversely, a class α ∈ π₂(X) is represented by a map S² → X with compact
     image. That image lies in a finite subcomplex K, so α = i_*(α′) and
     h_X(α) = i_*(h_K(α′)). If every finite subcomplex is Cockcroft, h_X(α) = 0.
     This gives (iv) ⇒ (ii).

6. **Consequence (b): infinitely many generators.** Let G be of type FP₂ and not
   finitely presented, with cd G = 2. Let K = ⟨S | R⟩ be aspherical, or merely
   Cockcroft, with S finite.
   - By step 4, R injects into N/[F,N]. This uses only cd G ≤ 2, not the
     augmentation-ideal hypothesis.
   - The Hopf sequence 0 → H₂(G) → N/[F,N] → F^ab gives rank N/[F,N] ≤ rank H₂(G) + |S|.
   - H₂(G; Z) is finitely generated, since G is FP₂.
   - So R is finite and G is finitely presented, a contradiction.
   - Hence S is infinite. Every presentation of G has R infinite, since G is not
     finitely presented. With T a maximal tree, X/T has 1-cell set S, so X has
     infinitely many 1-cells outside T.

7. **Bestvina--Brady kernels.** Let L be acyclic, not aspherical, finite and flag.
   - `H_L` has type FP but is not finitely presented, and cd `H_L` = 2 (Bestvina--Brady,
     Invent. Math. 129 (1997), Main Theorem; in this graph see
     `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`).
   - `H_L` is a finitely generated subgroup of the right-angled Artin group A_L. By
     step 6(c)–(d) of `cockcroft-rn-cd-two-asphericity-proof`,
     ⋂ Iⁿ(Z`H_L`) = 0.
   - (a) is (i) ⟺ (iii). (b) is step 6.
   - (c) The dichotomy `acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead`
     says that `H_L` refutes Eilenberg--Ganea or a Whitehead counterexample exists.
     - If (iii) holds, then gd `H_L` = 2 by (a), so `H_L` is not a counterexample to
       Eilenberg--Ganea.
     - So the second alternative holds.
   - (d) Let Y be a 2-dimensional K(`H_L`,1) and K ⊆ Y a finite subcomplex that is
     not aspherical.
     - K is Cockcroft by step 5.
     - Suppose cd π₁K ≤ 2.
       - If cd = 2, Gersten's finite criterion (arXiv:1501.06875, abstract) makes K
         aspherical: a finite 2-complex whose fundamental group has cd 2 is aspherical
         iff it has no spherical 2-cycles.
       - If cd ≤ 1, π₁K is free, so ⋂ Iⁿ = 0 (6(b) of the Theorem A proof, since free
         groups are residually torsion-free nilpotent). Theorem A then makes K
         aspherical.
       - Either way this is a contradiction.
     - Hence cd π₁K ≥ 3.

**Verification tier.**
- Steps 1–6 are complete given Theorem A, plus two standard facts: Lyndon's relation
  module identification and the Hopf formula.
- Step 7 uses Bestvina--Brady and Gersten as cited.
