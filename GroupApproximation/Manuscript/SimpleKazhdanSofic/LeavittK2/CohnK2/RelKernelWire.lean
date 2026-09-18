import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.RelKernelMain
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative kernel, wired into the cycle-break split

Lane sk-cohn-02 proves `CycleBreakRelativeKernelStatement` outright
(`relKer_cycleBreakRelativeKernel`). With it, stable `K₂(C_2(𝔽₂)) = 0` is exactly the Leavitt
endpoint, and the conjugation and base-change members of the cycle follow from that endpoint.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

/-- Stable `K₂(C_2(𝔽₂)) = 0` from the Leavitt endpoint alone. -/
theorem relKerWire_cohnStableK2_of_leavittK2 (hL : BinaryLeavittStableK2TrivialStatement) :
    BinaryCohnStableK2TrivialStatement :=
  cycleBreak_cohnStableK2_of_relativeKernel relKer_cycleBreakRelativeKernel hL

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKerWire_cohnStableK2_of_leavittK2

/-- The conjugation member of the cycle from the Leavitt endpoint alone. -/
theorem relKerWire_conj_of_leavittK2 (hL : BinaryLeavittStableK2TrivialStatement) :
    CohnBaseChangeConjStatement :=
  cycleBreak_conj_of_relativeKernel relKer_cycleBreakRelativeKernel hL

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKerWire_conj_of_leavittK2

/-- The base-change member of the cycle from the Leavitt endpoint alone. -/
theorem relKerWire_baseChange_of_leavittK2 (hL : BinaryLeavittStableK2TrivialStatement) :
    CohnBaseChangeK2Statement :=
  cycleBreak_baseChange_of_relativeKernel relKer_cycleBreakRelativeKernel hL

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKerWire_baseChange_of_leavittK2

/-- **Collapse.** Stable `K₂(C_2(𝔽₂)) = 0` is equivalent to the Leavitt endpoint. -/
theorem relKerWire_cohnStableK2_iff_leavittK2 :
    BinaryCohnStableK2TrivialStatement ↔ BinaryLeavittStableK2TrivialStatement :=
  ⟨binaryLeavittStableK2Trivial_of_cohnStableK2, relKerWire_cohnStableK2_of_leavittK2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKerWire_cohnStableK2_iff_leavittK2

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
