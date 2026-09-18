import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.UnitalModelUnitization
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureFunctorial
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWKK.StableFunctor
import GroupApproximation.Analysis.UniversalCoefficientTheorem

/-!
# From the `KKn`-commutative class to the unital UCT class

Lane TWWUCT-G (work order WO-TWWUCT-G), `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input).

Let `A` be a separable unital C⋆-algebra with a character `χ`, and let `J = ker χ`.  Split
exactness of `KK` (Blackadar 19.9.1, 20.1; Cuntz, K-Theory 1 (1987) §3) gives
`A ~ J ⊕ ℂ`, and likewise `C̃ ~ C ⊕ ℂ` for the unital model `C̃` of any `C`.  If `J` is
`KKn`-equivalent to a commutative `C`, then `A ~ J ⊕ ℂ ~ C ⊕ ℂ ~ C̃`, and `C̃` is unital and
commutative (Blackadar 22.3.5).  This file is the formal part of that argument, for an
arbitrary `KKn`-functor `F` with a `KKn`-bifunctor `P` (the direct sum) and a comparison
`UnitalComparison S F` with a stabilized homotopy functor `S` on unital algebras (for
`S = stabQ`, `F = stabQn` both have objects `𝒦 ⊗ qA`, and the comparison is the identity).

Contents:
* `kknEquivalent_of_split_models`, `exists_unitalModel_kknEquivalent`;
* `UnitalComparison S F`, `UnitalComparison.kkEquivalent`, `UnitalComparison.satisfiesUCT`;
* `satisfiesUCT_of_character_of_split_models`.
-/

namespace GroupApproximation.Full.TWWUCT.UnitalModel

open Bootstrap GroupApproximation.Full.TWWKK

noncomputable section

/-- **Transport along split models**: if `A ~ P(J, B)`, `U ~ P(C, B)` and `J ~ C`, then
`A ~ U`.  `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
theorem kknEquivalent_of_split_models {F : KKnFunctor} (P : KKnBifunctor F)
    {A U J C B : SepNUCStarAlgebra} (hA : F.KKnEquivalent A (P.objOp J B))
    (hU : F.KKnEquivalent U (P.objOp C B)) (hJC : F.KKnEquivalent J C) :
    F.KKnEquivalent A U :=
  KKnFunctor.KKnEquivalent.trans hA
    (KKnFunctor.KKnEquivalent.trans (P.kknEquivalent hJC (KKnFunctor.kknEquivalent_refl B))
      (KKnFunctor.KKnEquivalent.symm hU))

/-- **A unital algebra with a character whose kernel is in the class is `KKn`-equivalent to a
unital commutative model**, given the two split-exactness equivalences `A ~ P(ker χ, ℂ)` and
`C̃ ~ P(C, ℂ)` (Blackadar 22.3.5).  `non_mf_group_notes.tex`, `thm:fixed-radical-membership`
(UCT input). -/
theorem exists_unitalModel_kknEquivalent {F : KKnFunctor} (P : KKnBifunctor F) {A : Type}
    [CStarAlgebra A] [TopologicalSpace.SeparableSpace A] (χ : A →⋆ₐ[ℂ] ℂ)
    (hA : F.KKnEquivalent (SepNUCStarAlgebra.of A)
      (P.objOp (characterKernel χ) (SepNUCStarAlgebra.of ℂ)))
    (hU : ∀ C : SepNUCStarAlgebra,
      F.KKnEquivalent (SepNUCStarAlgebra.of (unitalModel C)) (P.objOp C (SepNUCStarAlgebra.of ℂ)))
    (hJ : F.IsKKnCommutative (characterKernel χ)) :
    ∃ C : SepNUCStarAlgebra, C.IsCommutative ∧
      F.KKnEquivalent (SepNUCStarAlgebra.of A) (SepNUCStarAlgebra.of (unitalModel C)) := by
  obtain ⟨C, hC, hJC⟩ := hJ
  exact ⟨C, hC, kknEquivalent_of_split_models P hA (hU C) hJC⟩

/-- **A comparison of a unital stabilized homotopy functor with a `KKn`-functor**: a map of
classes `F(A, B) → S(A, B)` for unital `A, B`, compatible with products and units.  For
`S = stabQ` and `F = stabQn` the two morphism sets are the same homotopy classes
`[𝒦 ⊗ qA, 𝒦 ⊗ qB]`, and the comparison is the identity.  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
structure UnitalComparison (S : TWWKK.StableFunctor) (F : KKnFunctor) where
  /-- The comparison map on classes. -/
  toHom : ∀ {A B : KK.SepCStarAlgebra.{0}},
    F.Hom (SepNUCStarAlgebra.of A) (SepNUCStarAlgebra.of B) → S.Hom A B
  /-- Products go to products. -/
  toHom_comp : ∀ {A B C : KK.SepCStarAlgebra.{0}}
    (y : F.Hom (SepNUCStarAlgebra.of B) (SepNUCStarAlgebra.of C))
    (x : F.Hom (SepNUCStarAlgebra.of A) (SepNUCStarAlgebra.of B)),
    toHom (F.comp y x) = S.comp (toHom y) (toHom x)
  /-- Units go to units. -/
  toHom_id : ∀ A : KK.SepCStarAlgebra.{0},
    toHom (F.idHom (SepNUCStarAlgebra.of A)) = HomotopyClass.id (S.obj A)

namespace UnitalComparison

variable {S : TWWKK.StableFunctor} {F : KKnFunctor} (Φ : UnitalComparison S F)

/-- **`KKn`-equivalence of unital algebras gives `KK`-equivalence.**
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (UCT input). -/
theorem kkEquivalent [∀ A B, AddCommGroup (S.Hom A B)] {A B : KK.SepCStarAlgebra.{0}}
    (h : F.KKnEquivalent (SepNUCStarAlgebra.of A) (SepNUCStarAlgebra.of B)) :
    S.toKasparovTheory.KKEquivalent A B := by
  obtain ⟨x, y, hyx, hxy⟩ := h
  refine ⟨Φ.toHom x, Φ.toHom y, ?_, ?_⟩
  · show S.comp (Φ.toHom y) (Φ.toHom x) = HomotopyClass.id (S.obj A)
    rw [← Φ.toHom_comp y x, hyx, Φ.toHom_id A]
  · show S.comp (Φ.toHom x) (Φ.toHom y) = HomotopyClass.id (S.obj B)
    rw [← Φ.toHom_comp x y, hxy, Φ.toHom_id B]

/-- **A unital algebra `KKn`-equivalent to the unital model of a commutative algebra satisfies
the UCT** (in the form `KasparovTheory.SatisfiesUCT`: `KK`-equivalence to a separable
commutative C⋆-algebra).  `non_mf_group_notes.tex`, `thm:fixed-radical-membership`
(UCT input). -/
theorem satisfiesUCT [∀ A B, AddCommGroup (S.Hom A B)] {A : KK.SepCStarAlgebra.{0}}
    {C : SepNUCStarAlgebra} (hC : C.IsCommutative)
    (h : F.KKnEquivalent (SepNUCStarAlgebra.of A) (SepNUCStarAlgebra.of (unitalModel C))) :
    S.toKasparovTheory.SatisfiesUCT A :=
  ⟨unitalModel C, unitalModel_isCommutative hC, Φ.kkEquivalent h⟩

end UnitalComparison

/-- **The UCT for a unital algebra with a character whose kernel is `KKn`-commutative**, given
the split-exactness equivalences `A ~ P(ker χ, ℂ)` and `C̃ ~ P(C, ℂ)` (Blackadar 19.9.1,
22.3.5; Rosenberg--Schochet, Duke Math. J. 55 (1987), §2).  `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (UCT input). -/
theorem satisfiesUCT_of_character_of_split_models {S : TWWKK.StableFunctor} {F : KKnFunctor}
    [∀ A B, AddCommGroup (S.Hom A B)] (Φ : UnitalComparison S F) (P : KKnBifunctor F)
    {A : KK.SepCStarAlgebra.{0}} (χ : A →⋆ₐ[ℂ] ℂ)
    (hA : F.KKnEquivalent (SepNUCStarAlgebra.of A)
      (P.objOp (characterKernel χ) (SepNUCStarAlgebra.of ℂ)))
    (hU : ∀ C : SepNUCStarAlgebra,
      F.KKnEquivalent (SepNUCStarAlgebra.of (unitalModel C)) (P.objOp C (SepNUCStarAlgebra.of ℂ)))
    (hJ : F.IsKKnCommutative (characterKernel χ)) :
    S.toKasparovTheory.SatisfiesUCT A := by
  obtain ⟨C, hC, hAC⟩ := exists_unitalModel_kknEquivalent P χ hA hU hJ
  exact Φ.satisfiesUCT hC hAC

end

end GroupApproximation.Full.TWWUCT.UnitalModel
