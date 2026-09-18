import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.Endpoint
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.Main
import GroupApproximation.Meta.AxiomGuard

/-!
# Brown wired I: lane 14's criterion inputs, unconditional (lane sk-leavitt-29)

Let `L = L_{𝔽₂}(1,2)`.  Lane sk-leavitt-20 proved `BrownBridge.brownExtension :
Criterion.BrownExtensionStatement`.  Every consumer of `BrownExtensionStatement` in the tree is
`EdgeTriangleLift/Endpoint.lean:79` or `:88`, or the bundle `Criterion.RankFourCriterionInputsStatement`.
This file plugs `brownExtension` into all three.

* `rankFourCriterionInputs_holds`: Brown's extension and the vertex lift together.
* `rankFourInjective_of_stabKernelThreeTrivial_holds`: `stab K₂(3, L) = ⊥ → K₂(4, L) = ⊥`.
* `rankFourInjectiveOfStabKernelThreeTrivial_holds`: lane 14's interface
  `EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement`, which is `h14` in
  `LeavittK2/Endpoints.lean`.

## Truth check

These are true, and only reassemble proved pieces: Khanh's criterion at `n = 4` (Brown extension
plus the vertex lift).  Nothing new is proved here.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Criterion

/-- **Lane 14's inputs, unconditional**: Brown's extension property and the rank-four lift. -/
theorem rankFourCriterionInputs_holds : RankFourCriterionInputsStatement :=
  ⟨GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.brownExtension,
    rankFourLift⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.rankFourCriterionInputs_holds

/-- **Khanh's criterion at `n = 4`, unconditional.**  `stab (K₂(3, L)) = ⊥` implies
`K₂(4, L) = ⊥`. -/
theorem rankFourInjective_of_stabKernelThreeTrivial_holds :
    EndpointInterfaces.BinaryLeavittStabKernelThreeTrivialStatement →
      LeavittFP.BinaryLeavittSteinbergRankFourInjectiveStatement :=
  rankFourInjective_of_stabKernelThreeTrivial_of_brownExtension
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.brownExtension

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.rankFourInjective_of_stabKernelThreeTrivial_holds

/-- **Lane 14's interface, unconditional**: `EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement`. -/
theorem rankFourInjectiveOfStabKernelThreeTrivial_holds :
    EndpointInterfaces.RankFourInjectiveOfStabKernelThreeTrivialStatement :=
  rankFourInjectiveOfStabKernelThreeTrivial_of_brownExtension
    GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BrownBridge.brownExtension

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift.rankFourInjectiveOfStabKernelThreeTrivial_holds

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.EdgeTriangleLift
