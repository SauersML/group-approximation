import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.SteinbergIso
import GroupApproximation.Manuscript.SimpleKazhdanSofic.FPSimpleKazhdan.CapraceRemyGap
import GroupApproximation.Steinberg.QuotientExactness
import GroupApproximation.Leavitt.FinitePresentation
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Meta.AxiomGuard

/-!
# `St_5(L_{𝔽₂}(1,2))` is finitely presented; the remaining gap is `K₂ = ⊥`

Let `L = L_{𝔽₂}(1,2)` (`BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)`).  The gap
`FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement` asks for a finite presentation of
`EL_5(L)`.  This module proves half of it unconditionally and isolates the other half.

## Route, and why it was chosen

`BooneHigman.SteinbergBasic.isFinitelyPresented_elementaryGroup_of_K2_eq_bot` gives
`EL_5(L)` finitely presented from two inputs: `St_5(L)` finitely presented, and `K₂(5, L) = ⊥`.
The cheapest path to the first input avoids Khanh's unit-group presentation.  It uses only the
library's Steinberg exactness and a direct presentation of Steinberg groups over free rings:

1. `LeavittFP.FreePresentation`, `WordCalculus`, `RootExtension`, `SteinbergIso`: for a finite alphabet
   `X`, the group `KMGroup X` is given by finitely many generators `x_{ij}(1)`, `x_{ij}(a)` (`a ∈ X`)
   and finitely many relators.  It is isomorphic to `St_5(ℤ⟨X⟩)` (a special case of Krstić–McCool).
   So `St_5(ℤ⟨X⟩)` is finitely presented (`steinbergFreeAlgebra_isFinitelyPresented`).
2. `L = ℤ⟨s₀, s₁, t₀, t₁⟩ / (six relators)` (`BinaryLeavittAbsolute.ringEquiv`,
   `relationPairs_finite`).  So the kernel of `leavittQuotientMap : ℤ⟨X⟩ → L` is the two-sided span
   of a finite set (`ker_leavittQuotientMap`).
3. `SteinbergGroup.ringMap_ker_isFinitelyNormallyGenerated_of_ker_eq_span` shows that
   `St_5(ℤ⟨X⟩) → St_5(L)` is surjective with finitely normally generated kernel.  Hence `St_5(L)` is
   finitely presented (`steinbergLeavitt_isFinitelyPresented`).

## The gap

`BinaryLeavittSteinbergInjectiveStatement`: `K₂(Fin 5, L) = ⊥`, i.e. `St_5(L) → EL_5(L)` is
injective.  It is strictly smaller than the old gap, because it no longer mentions any finite
presentation.  It is true by Khanh (arXiv:2609.08428), Theorem 5.4: `St_r(L) → GL_r(L)` is an
isomorphism for `r ≥ 3`.  Its image is `E_r(L)`, and `E_r(L) = GL_r(L)` by Lemma 5.3.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

noncomputable section

/-- The quotient map `ℤ⟨s₀, s₁, t₀, t₁⟩ → L_{𝔽₂}(1,2)`. -/
def leavittQuotientMap :
    BinaryLeavittAbsolute.Free →+* BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2) :=
  BinaryLeavittAbsolute.ringEquiv.symm.toRingHom.comp
    (RingQuot.mkRingHom BinaryLeavittAbsolute.Relation)

theorem leavittQuotientMap_apply (x : BinaryLeavittAbsolute.Free) :
    leavittQuotientMap x =
      BinaryLeavittAbsolute.ringEquiv.symm (RingQuot.mkRingHom BinaryLeavittAbsolute.Relation x) :=
  rfl

theorem leavittQuotientMap_surjective : Function.Surjective leavittQuotientMap := by
  intro y
  obtain ⟨z, rfl⟩ := BinaryLeavittAbsolute.ringEquiv.symm.surjective y
  obtain ⟨x, rfl⟩ := RingQuot.mkRingHom_surjective BinaryLeavittAbsolute.Relation z
  exact ⟨x, rfl⟩

/-- The six Leavitt relators, as differences. -/
def leavittRelators : Set BinaryLeavittAbsolute.Free :=
  (fun p : BinaryLeavittAbsolute.Free × BinaryLeavittAbsolute.Free => p.1 - p.2) ''
    {p | BinaryLeavittAbsolute.Relation p.1 p.2}

theorem leavittRelators_finite : leavittRelators.Finite :=
  BinaryLeavittAbsolute.relationPairs_finite.image _

/-- The kernel of the quotient map is spanned by the finitely many relators. -/
theorem ker_leavittQuotientMap :
    TwoSidedIdeal.ker leavittQuotientMap = TwoSidedIdeal.span leavittRelators := by
  apply le_antisymm
  · intro z hz
    rw [TwoSidedIdeal.mem_ker, leavittQuotientMap_apply, RingEquiv.map_eq_zero_iff] at hz
    have w : ∀ ⦃x y : BinaryLeavittAbsolute.Free⦄, BinaryLeavittAbsolute.Relation x y →
        (TwoSidedIdeal.span leavittRelators).ringCon.mk' x =
          (TwoSidedIdeal.span leavittRelators).ringCon.mk' y := by
      intro x y h
      have hK : x - y ∈ leavittRelators := by
        change x - y ∈ (fun p : BinaryLeavittAbsolute.Free × BinaryLeavittAbsolute.Free =>
          p.1 - p.2) '' {p | BinaryLeavittAbsolute.Relation p.1 p.2}
        exact ⟨(x, y), h, rfl⟩
      have hmem : x - y ∈ TwoSidedIdeal.ker (TwoSidedIdeal.span leavittRelators).ringCon.mk' := by
        rw [TwoSidedIdeal.ker_ringCon_mk']
        exact TwoSidedIdeal.subset_span hK
      rwa [TwoSidedIdeal.mem_ker, map_sub, sub_eq_zero] at hmem
    have hz' := RingQuot.lift_mkRingHom_apply (TwoSidedIdeal.span leavittRelators).ringCon.mk'
      (r := BinaryLeavittAbsolute.Relation) w z
    rw [hz, map_zero] at hz'
    have h3 : z ∈ TwoSidedIdeal.ker (TwoSidedIdeal.span leavittRelators).ringCon.mk' := by
      rw [TwoSidedIdeal.mem_ker]
      exact hz'.symm
    rwa [TwoSidedIdeal.ker_ringCon_mk'] at h3
  · rw [TwoSidedIdeal.span_le]
    intro z hz
    change z ∈ (fun p : BinaryLeavittAbsolute.Free × BinaryLeavittAbsolute.Free => p.1 - p.2) ''
      {p | BinaryLeavittAbsolute.Relation p.1 p.2} at hz
    obtain ⟨⟨x, y⟩, h, rfl⟩ := hz
    have h' : BinaryLeavittAbsolute.Relation x y := h
    show x - y ∈ TwoSidedIdeal.ker leavittQuotientMap
    rw [TwoSidedIdeal.mem_ker, map_sub, sub_eq_zero, leavittQuotientMap_apply,
      leavittQuotientMap_apply, RingQuot.mkRingHom_rel h']

/-- `St_5(L_{𝔽₂}(1,2))` is finitely presented. -/
theorem steinbergLeavitt_isFinitelyPresented :
    Group.IsFinitelyPresented
      (SteinbergGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) := by
  haveI := steinbergFreeAlgebra_isFinitelyPresented BinaryLeavitt.Generator
  exact Group.IsFinitelyPresented.of_surjective
    (SteinbergGroup.ringMap (I := Fin 5) leavittQuotientMap)
    (SteinbergGroup.ringMap_surjective_of_surjective leavittQuotientMap
      leavittQuotientMap_surjective)
    (SteinbergGroup.ringMap_ker_isFinitelyNormallyGenerated_of_ker_eq_span leavittQuotientMap
      leavittQuotientMap_surjective (by simp) leavittRelators leavittRelators_finite
      ker_leavittQuotientMap)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.steinbergLeavitt_isFinitelyPresented

/-- **The gap.**  The Steinberg map `St_5(L_{𝔽₂}(1,2)) → EL_5(L_{𝔽₂}(1,2))` is injective, i.e.
`K₂(5, L) = ⊥`.  True by Khanh (arXiv:2609.08428), Theorem 5.4 with Lemma 5.3; not proved here. -/
def BinaryLeavittSteinbergInjectiveStatement : Prop :=
  BooneHigman.SteinbergBasic.K2 (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) = ⊥

/-- `EL_5(L_{𝔽₂}(1,2))` is finitely presented, from the smaller gap `K₂(5, L) = ⊥`. -/
theorem binaryLeavittElementaryFinitelyPresented_of_binaryLeavittSteinbergInjective
    (h : BinaryLeavittSteinbergInjectiveStatement) :
    FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement := by
  haveI := steinbergLeavitt_isFinitelyPresented
  have h2 : Group.IsFinitelyPresented
      ↥(elementaryGroup (Fin 5) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :=
    BooneHigman.SteinbergBasic.isFinitelyPresented_elementaryGroup_of_K2_eq_bot h
  exact h2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.binaryLeavittElementaryFinitelyPresented_of_binaryLeavittSteinbergInjective

/-- **tex l.733–737**, the whole sentence, from the smaller gap `K₂(5, L_{𝔽₂}(1,2)) = ⊥`. -/
theorem manuscriptSentence_finitelyPresentedCase_of_binaryLeavittSteinbergInjective
    (h : BinaryLeavittSteinbergInjectiveStatement) :
    (∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E) ∧
    (∀ (E : Type) [Group E], Group.IsFinitelyPresented E → IsLEF E → IsResiduallyFinite E) ∧
      (∀ (E : Type) [Group E] [IsSimpleGroup E] [Infinite E], ¬ IsResiduallyFinite E) ∧
      ∀ (Λ : Type) [Group Λ] [Group.FG Λ] (Z : Type) [TopologicalSpace Z] [CompactSpace Z]
        [TopologicalSpace.MetrizableSpace Z] [TotallyDisconnectedSpace Z] [PerfectSpace Z]
        [Nonempty Z] [MulAction Λ Z] [ContinuousConstSMul Λ Z], MulAction.IsMinimal Λ Z →
        (∀ ξ : Λ, ξ ≠ 1 → ∀ U : Set Z, IsOpen U → U.Nonempty → ∃ z ∈ U, ξ • z ≠ z) →
        ∀ S : Finset (ClopenGroupCrossedProduct Λ Z (ZMod 2)), 1 ∈ S →
          Subring.closure (S : Set (ClopenGroupCrossedProduct Λ Z (ZMod 2))) = ⊤ →
        ∀ (N : ℕ → ℕ)
          (φ : ∀ k, ClopenGroupCrossedProduct Λ Z (ZMod 2) → Matrix (Fin (N k)) (Fin (N k)) (ZMod 2)),
          IsMatricialVia S N φ → ∀ n : ℕ, 3 ≤ n →
            ¬ Group.IsFinitelyPresented
              ↥(elementaryGroup (Fin n) (ClopenGroupCrossedProduct Λ Z (ZMod 2))) :=
  FPSimpleKazhdan.manuscriptSentence_finitelyPresentedCase_of_binaryLeavittElementaryFinitelyPresented
    (binaryLeavittElementaryFinitelyPresented_of_binaryLeavittSteinbergInjective h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.manuscriptSentence_finitelyPresentedCase_of_binaryLeavittSteinbergInjective

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP
