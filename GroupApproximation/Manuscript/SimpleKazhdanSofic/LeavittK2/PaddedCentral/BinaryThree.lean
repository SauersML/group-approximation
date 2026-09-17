import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.PaddedCentral
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.KernelCommutator.Padded
import GroupApproximation.Meta.AxiomGuard

/-!
# Discharging lane 04's padded-centrality interface (lane sk-leavitt-03)

Lane sk-leavitt-04 (`KernelCommutator.Padded`) states `BinaryLeavittPaddedCentralThreeStatement`,
the special case `n = 3`, `R = L_{𝔽₂}(1,2)` of lane 03's endpoint.  Here we prove it from
`map_stab_K2_le_center`.  That also closes lane 04's reduction
`stabKernelThreeTrivialOfSuperperfect_of_paddedCentral`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

/-- Lane 04's interface `BinaryLeavittPaddedCentralThreeStatement` holds. -/
theorem binaryLeavittPaddedCentralThreeStatement_holds :
    BinaryLeavittPaddedCentralThreeStatement := by
  unfold BinaryLeavittPaddedCentralThreeStatement
  exact map_stab_K2_le_center

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittPaddedCentralThreeStatement_holds

/-- Padded centrality closes lane 04's rank-three reduction. -/
theorem stabKernelThreeTrivialOfSuperperfect_holds :
    EndpointInterfaces.StabKernelThreeTrivialOfSuperperfectStatement :=
  stabKernelThreeTrivialOfSuperperfect_of_paddedCentral
    binaryLeavittPaddedCentralThreeStatement_holds

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.stabKernelThreeTrivialOfSuperperfect_holds

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
