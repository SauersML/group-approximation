import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownWired.Criterion
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Endpoints
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral.BinaryThree
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown wired II: tex l.730–735 from superperfect units alone (lane sk-leavitt-29)

`LeavittK2/Endpoints.lean` takes three hypotheses `h04 h14 hsp`.  Both interface hypotheses are
now proved:

* `h04 = LeavittK2.stabKernelThreeTrivialOfSuperperfect_holds` (`PaddedCentral/BinaryThree.lean:25`);
* `h14 = EdgeTriangleLift.rankFourInjectiveOfStabKernelThreeTrivial_holds` (`BrownWired/Criterion`).

So each endpoint below takes only `hsp`.

## Remaining gap

`EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement` (`LeavittK2/EndpointInterfaces.lean:45`),
superperfectness of `L_{𝔽₂}(1,2)ˣ`.  It is true (Khanh, arXiv:2609.08428, Thm 2.2) but not proved
in Lean.  With Brown wired it is *equivalent* to `K₂(4, L) = ⊥`, see
`binaryLeavittRankFourInjective_iff_unitsSuperperfect` in `BrownWired/Stable`.

## Truth check

Every conclusion is true.  The universe levels `HasKazhdanPropertyT.{0, 0}` and `E : Type` are
copied verbatim from `LeavittK2/Endpoints.lean:84–112`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift

open GroupApproximation.SimpleKazhdanSofic SymbolicDynamics.FullShift

/-- `K₂(4, L_{𝔽₂}(1,2)) = ⊥` from superperfect units alone. -/
theorem binaryLeavittRankFourInjective_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittRankFourInjective_of_superperfect
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivialOfSuperperfect_holds
    rankFourInjectiveOfStabKernelThreeTrivial_holds hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.binaryLeavittRankFourInjective_of_unitsSuperperfect

/-- `K₂(4, L_{𝔽₂}(1,2))` is finitely normally generated, from superperfect units alone. -/
theorem binaryLeavittRankFourK2FinitelyNormallyGenerated_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    LeavittFP.BinaryLeavittSteinbergRankFourK2FinitelyNormallyGeneratedStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittRankFourK2FinitelyNormallyGenerated_of_superperfect
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivialOfSuperperfect_holds
    rankFourInjectiveOfStabKernelThreeTrivial_holds hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.binaryLeavittRankFourK2FinitelyNormallyGenerated_of_unitsSuperperfect

/-- `EL_5(L_{𝔽₂}(1,2))` is finitely presented, from superperfect units alone. -/
theorem binaryLeavittElementaryFinitelyPresented_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    FPSimpleKazhdan.BinaryLeavittElementaryFinitelyPresentedStatement :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittElementaryFinitelyPresented_of_superperfect
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivialOfSuperperfect_holds
    rankFourInjectiveOfStabKernelThreeTrivial_holds hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.binaryLeavittElementaryFinitelyPresented_of_unitsSuperperfect

/-- **tex l.733–735, existence clause**, from superperfect units alone. -/
theorem manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_unitsSuperperfect
    (hsp : EndpointInterfaces.BinaryLeavittUnitsSuperperfectStatement) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ Group.IsFinitelyPresented E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E :=
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_binaryLeavittUnitsSuperperfect
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivialOfSuperperfect_holds
    rankFourInjectiveOfStabKernelThreeTrivial_holds hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.manuscriptSentence_infiniteFinitelyPresentedSimpleKazhdanGroupsExist_of_unitsSuperperfect

/-- **tex l.730–735**, the finitely presented case, from superperfect units alone. -/
theorem manuscriptSentence_finitelyPresentedCase_of_unitsSuperperfect
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
  GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.manuscriptSentence_finitelyPresentedCase_of_binaryLeavittUnitsSuperperfect
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivialOfSuperperfect_holds
    rankFourInjectiveOfStabKernelThreeTrivial_holds hsp

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.manuscriptSentence_finitelyPresentedCase_of_unitsSuperperfect

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift
