import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.Padded
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.PaddedCentrality.Reduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Endpoints with lane 04 discharged (lane sk-leavitt-15, refinement)

Census row `768ac9454e9b` (tex l.733–735):

> Infinite finitely presented simple Kazhdan groups exist~\cite{CapraceRemy}, and whether one of
> them is sofic, or at least hyperlinear, remains open.

The sibling module `LeavittK2.Endpoints` proves the sentence from three hypotheses: the lane 04
interface `EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement`, the lane 14 interface
`EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement`, and
`EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement`.

Lane 04 has since landed (`LeavittK2.KernelCommutator.Padded`).  Its theorem
`stabKernelThreeTrivialOfSuperperfect_of_paddedCentral` discharges the lane 04 interface from
`BinaryLeavittPaddedCentralThreeStatement`, which is padded centrality (Khanh Lemma 5.6) at
`n = 3`, `R = L`.  This module substitutes it into the endpoints.

## Why the new hypothesis set is strictly smaller in proof content

The lane 04 interface was the whole argument "a perfect central extension of `E_3(L) ≅ Lˣ`
collapses, then `stab` kills the commutator".  That argument is now proved in Lean
(`K2_three_le_commutator_of_superperfect`, `stabKernelThreeTrivial_of_paddedCentral_of_superperfect`).
What remains in its place is a single Steinberg commutator identity: `stab (K₂(3, L))` is central
in `St_4(L)`.  This holds over every ring (Khanh Lemma 5.6), and it is trivially true here because
`K₂(3, L) = ⊥` (Khanh Thm 5.4).  The two other hypotheses are unchanged.

The census lane `sk-rows-14` states the ring-generic target
`SkRows.PaddedCentrality.PaddedCentralityStatement m R`.  At `m = 3`, `R = L` its body is the same
term as `BinaryLeavittPaddedCentralThreeStatement`, so it discharges the hypothesis by definitional
unfolding (`binaryLeavittPaddedCentralThree_of_paddedCentralityStatement`).  It in turn follows from
the column/row action formula `SkRows.PaddedCentrality.SteinbergColumnActionStatement 3 L`
(`binaryLeavittPaddedCentralThree_of_columnAction`).

## Truth check

All hypotheses are true.  Padded centrality is Khanh Lemma 5.6.  The column/row action is the
standard conjugation formula (see the truth check in `SkRows.PaddedCentrality.Statement`).  The
lane 14 criterion is Khanh Thm 5.1 at `n = 4`, and superperfectness is Khanh Thm 2.2.
The "remains open" clause of the sentence is attribution only.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- The ring-generic padded centrality target of lane `sk-rows-14`, at `m = 3` and
`R = L_{𝔽₂}(1,2)`, is lane 04's rank-three padded centrality hypothesis. -/
theorem binaryLeavittPaddedCentralThree_of_paddedCentralityStatement
    (h : GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.PaddedCentralityStatement 3
      (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
    BinaryLeavittPaddedCentralThreeStatement :=
  h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittPaddedCentralThree_of_paddedCentralityStatement

/-- Rank-three padded centrality over `L_{𝔽₂}(1,2)` from the column/row action formula
(lane `sk-rows-13` interface, reduced by lane `sk-rows-14`). -/
theorem binaryLeavittPaddedCentralThree_of_columnAction
    (h : GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.SteinbergColumnActionStatement
      3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
    BinaryLeavittPaddedCentralThreeStatement :=
  binaryLeavittPaddedCentralThree_of_paddedCentralityStatement
    (GroupApproximation.SimpleKazhdanSofic.SkRows.PaddedCentrality.paddedCentralityStatement_of_columnAction
      3 (GroupApproximation.BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) h)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittPaddedCentralThree_of_columnAction

/-- **The live gap `K2RankFourEndpoints.lean:59`**, with lane 04 discharged: `K₂(4, L_{𝔽₂}(1,2))`
is finitely normally generated, from padded centrality, the lane 14 criterion and superperfect
units. -/
theorem binaryLeavittRankFourK2FinitelyNormallyGenerated_of_paddedCentral_of_superperfect
    (hc : BinaryLeavittPaddedCentralThreeStatement)
    (h14 : EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement)
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement :=
  binaryLeavittRankFourK2FinitelyNormallyGenerated_of_superperfect
    (stabKernelThreeTrivialOfSuperperfect_of_paddedCentral hc) h14 hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittRankFourK2FinitelyNormallyGenerated_of_paddedCentral_of_superperfect

/-- **The gap `CapraceRemyGap.lean:92`**, with lane 04 discharged: `EL_5(L_{𝔽₂}(1,2))` is finitely
presented. -/
theorem binaryLeavittElementaryFinitelyPresented_of_paddedCentral_of_superperfect
    (hc : BinaryLeavittPaddedCentralThreeStatement)
    (h14 : EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement)
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement :=
  binaryLeavittElementaryFinitelyPresented_of_superperfect
    (stabKernelThreeTrivialOfSuperperfect_of_paddedCentral hc) h14 hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittElementaryFinitelyPresented_of_paddedCentral_of_superperfect

/-- **tex l.733–735, existence clause** (row `768ac9454e9b`), with lane 04 discharged: there is an
infinite, finitely presented, simple group with property (T), namely `EL_5(L_{𝔽₂}(1,2))`. -/
theorem manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_paddedCentral_of_superperfect
    (hc : BinaryLeavittPaddedCentralThreeStatement)
    (h14 : EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement)
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E :=
  manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittUnitsSuperperfect
    (stabKernelThreeTrivialOfSuperperfect_of_paddedCentral hc) h14 hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_paddedCentral_of_superperfect

/-- **tex l.730–735**, the finitely presented case, with lane 04 discharged.  The existence clause
(row `768ac9454e9b`) is conditional on padded centrality, the lane 14 criterion and superperfect
units.  The other clauses (row `e19e0d3328ad`) are proved. -/
theorem manuscriptSentence_finitelyPresentedCase_of_paddedCentral_of_superperfect
    (hc : BinaryLeavittPaddedCentralThreeStatement)
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
  manuscriptSentence_finitelyPresentedCase_of_binaryLeavittUnitsSuperperfect
    (stabKernelThreeTrivialOfSuperperfect_of_paddedCentral hc) h14 hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.manuscriptSentence_finitelyPresentedCase_of_paddedCentral_of_superperfect

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
