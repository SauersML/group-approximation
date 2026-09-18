import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EndpointInterfaces
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RankFourEndpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# Endpoints: tex l.733–735 from superperfectness of `L_{𝔽₂}(1,2)ˣ` (lane sk-leavitt-15)

Census row `768ac9454e9b` (tex l.733–735):

> Infinite finitely presented simple Kazhdan groups exist~\cite{CapraceRemy}, and whether one of
> them is sofic, or at least hyperlinear, remains open.

The old key `460d289c5b0f` (tex l.733–737) is superseded.  Its clauses now sit in rows
`768ac9454e9b` (existence clause, this module) and `e19e0d3328ad` (tex l.730–732, already closed by
`AbstractIntro.manuscriptSentence_generalLimitsNotFinitelyPresented`).

## Route

Let `L = L_{𝔽₂}(1,2)` and `hsp : BinaryLeavittUnitsSuperperfectStatement`.
1. Lane 04 interface: `stab (K₂(3, L)) = ⊥`.
2. Lane 14 interface: `K₂(4, L) = ⊥` (`LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement`).
3. `LeavittFP.rankFourK2FinitelyNormallyGenerated_of_rankFourInjective`: `K₂(4, L)` is finitely
   normally generated.  This is the live gap `K2RankFourEndpoints.lean:59`.
4. `LeavittFP.binaryLeavittElementaryFinitelyPresented_of_rankFourK2FinitelyNormallyGenerated`:
   `EL_5(L)` is finitely presented, which is the gap `FPSimpleKazhdan/CapraceRemyGap.lean:92`.
5. `LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFourK2FinitelyNormallyGenerated`:
   the sentence.

## Remaining gap, and honesty about its strength

The endpoints assume `BinaryLeavittUnitsSuperperfectStatement` (`H₂(Lˣ) = 0`), together with the
interfaces of lanes 04 and 14 until those lanes land.  The superperfect statement mentions no
Steinberg group, no frame complex and no presentation.  In proof content it is smaller than the
live gap: it drops Khanh's criterion (lanes 01–14).  It is NOT logically weaker once the lanes are
in.  `K₂(5, L) = ⊥`, Kervaire–Steinberg splitting and `GL_5(L) ≅ Lˣ` give superperfectness back,
so in the presence of the corpus the two statements are equivalent.  The irreducible input is
Khanh Thm 2.2 (acyclicity of `Lˣ`).  The "remains open" clause of the sentence is attribution only.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- `K₂(4, L_{𝔽₂}(1,2)) = ⊥` from superperfect units, through the interfaces of lanes 04 and 14. -/
theorem binaryLeavittRankFourInjective_of_superperfect
    (h04 : EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement)
    (h14 : EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement)
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  h14 (h04 hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittRankFourInjective_of_superperfect

/-- **The live gap `K2RankFourEndpoints.lean:59`** from superperfect units: `K₂(4, L_{𝔽₂}(1,2))`
is finitely normally generated. -/
theorem binaryLeavittRankFourK2FinitelyNormallyGenerated_of_superperfect
    (h04 : EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement)
    (h14 : EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement)
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement :=
  LeavittFP.rankFourK2FinitelyNormallyGenerated_of_rankFourInjective
    (binaryLeavittRankFourInjective_of_superperfect h04 h14 hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittRankFourK2FinitelyNormallyGenerated_of_superperfect

/-- **The gap `CapraceRemyGap.lean:92`** from superperfect units: `EL_5(L_{𝔽₂}(1,2))` is finitely
presented. -/
theorem binaryLeavittElementaryFinitelyPresented_of_superperfect
    (h04 : EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement)
    (h14 : EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement)
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement :=
  LeavittFP.binaryLeavittElementaryFinitelyPresented_of_rankFourK2FinitelyNormallyGenerated
    (binaryLeavittRankFourK2FinitelyNormallyGenerated_of_superperfect h04 h14 hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittElementaryFinitelyPresented_of_superperfect

/-- **tex l.733–735, existence clause** (row `768ac9454e9b`), from superperfect units: there is an
infinite, finitely presented, simple group with property (T), namely `EL_5(L_{𝔽₂}(1,2))`. -/
theorem manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittUnitsSuperperfect
    (h04 : EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement)
    (h14 : EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement)
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E :=
  FPSimpleKazhdan.manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittElementaryFinitelyPresented
    (binaryLeavittElementaryFinitelyPresented_of_superperfect h04 h14 hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittUnitsSuperperfect

/-- **tex l.730–735**, the finitely presented case, from superperfect units.  The existence clause
(row `768ac9454e9b`) is conditional.  The other clauses (row `e19e0d3328ad`) are the closed
`AbstractIntro.manuscriptSentence_generalLimitsNotFinitelyPresented`. -/
theorem manuscriptSentence_finitelyPresentedCase_of_binaryLeavittUnitsSuperperfect
    (h04 : EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement)
    (h14 : EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement)
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
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
  LeavittFP.manuscriptSentence_finitelyPresentedCase_of_rankFourK2FinitelyNormallyGenerated
    (binaryLeavittRankFourK2FinitelyNormallyGenerated_of_superperfect h04 h14 hsp)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.manuscriptSentence_finitelyPresentedCase_of_binaryLeavittUnitsSuperperfect

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
