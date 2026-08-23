import GroupApproximation.Sofic.LiteralBaseP13PropertyTBridge
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.MarkedCompressionSequentialKill

/-!
# Minimal non-MF certificate for the literal group

This module contains only the marked-compression datum and its operator-MF
obstruction.  Operator-algebraic consequences belong to the larger endpoint
module and are not dependencies of this certificate.
-/

namespace GroupApproximation
namespace LiteralNonMFEndpoint

open LiteralNonMFPresentation

noncomputable section

/-- The marked-compression datum for the literal group. -/
noncomputable def inclusionData :
    MarkedCompressionInclusionData Base MarkedGroup where
  iota := baseMap
  t := stable
  c := lamp
  a := PresentedGroup.of v1Index
  kazhdan := LiteralBaseP13PropertyTBridge.base_hasKazhdanPropertyT
  compresses gamma := by
    obtain ⟨delta, hdelta⟩ := stable_conjugates_base_into_base gamma
    exact ⟨delta, hdelta.symm⟩
  comm_c := lamp_commutes_base
  word_sq := by
    rw [← mark_eq_markedCompressionWord]
    exact mark_sq
  word_central g := by
    rw [← mark_eq_markedCompressionWord]
    exact mark_central g

@[simp] theorem inclusionData_word : inclusionData.word = mark :=
  mark_eq_markedCompressionWord.symm

/-- Every norm-matrix-corona representation kills the literal marked word. -/
theorem literal_mark_normMFInvisible : NormMFInvisible mark := by
  rw [← inclusionData_word]
  exact inclusionData.word_normMFInvisible

end

end LiteralNonMFEndpoint
end GroupApproximation
