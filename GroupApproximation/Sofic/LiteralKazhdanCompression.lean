import GroupApproximation.Kazhdan.LiteralBaseSOS
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.MarkedCompressionSequentialKill

/-!
# The literal presentation as marked Kazhdan-compression data

This file connects the manuscript's literal eight-generator presentation to
the general analytic obstruction.  Every group-theoretic field is discharged
from the displayed relators.  The only input left explicit is property `(T)`
of the literal six-generator base; alternatively, an exact rational
sum-of-squares certificate supplies that input through `LiteralBaseSOS`.

Thus this module pinpoints the formal trust boundary without replacing the
literal group by the independent Shalom-cover witness.
-/

namespace GroupApproximation
namespace LiteralKazhdanCompression

open LiteralNonMFPresentation

/-- The literal presentation supplies the exact marked-compression data once
property `(T)` of its six-generator base is given. -/
noncomputable def data (hT : HasKazhdanPropertyT.{0, 0} Base) :
    MarkedCompressionInclusionData Base MarkedGroup where
  iota := baseMap
  t := stable
  c := lamp
  a := PresentedGroup.of v1Index
  kazhdan := hT
  compresses := by
    intro g
    rcases stable_conjugates_base_into_base g with ⟨h, hh⟩
    exact ⟨h, hh.symm⟩
  comm_c := lamp_commutes_base
  word_sq := by
    rw [← mark_eq_markedCompressionWord]
    exact mark_sq
  word_central := by
    intro g
    rw [← mark_eq_markedCompressionWord]
    exact mark_central g

/-- The abstract marked-compression word is literally the marked word of the
printed presentation. -/
@[simp] theorem data_word (hT : HasKazhdanPropertyT.{0, 0} Base) :
    (data hT).word = mark :=
  mark_eq_markedCompressionWord.symm

/-- Conditional literal universal-kernel theorem: property `(T)` of the
displayed six-generator base forces its marked word into the norm-MF
residual. -/
theorem mark_normMFInvisible_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    NormMFInvisible mark := by
  rw [← data_word hT]
  exact (data hT).word_normMFInvisible

/-- Conditional literal non-MF endpoint under exactly the remaining
property-`(T)` input. -/
theorem not_isOperatorMF_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ IsOperatorMF MarkedGroup := by
  apply (data hT).not_isOperatorMF
  simpa only [data_word] using LiteralNonMFLinearWitness.literal_mark_ne_one

/-- An exact rational SOS certificate closes the literal universal-kernel
endpoint without an additional property-`(T)` axiom. -/
theorem mark_normMFInvisible_of_isRationalCertificate {c : ℚ}
    (hcert : LiteralBaseSOS.IsRationalCertificate c) :
    NormMFInvisible mark :=
  mark_normMFInvisible_of_hasKazhdanPropertyT
    (LiteralBaseSOS.base_hasKazhdanPropertyT_of_isRationalCertificate hcert)

/-- An exact rational SOS certificate proves that the literal printed group
is not operator-MF. -/
theorem not_isOperatorMF_of_isRationalCertificate {c : ℚ}
    (hcert : LiteralBaseSOS.IsRationalCertificate c) :
    ¬ IsOperatorMF MarkedGroup :=
  not_isOperatorMF_of_hasKazhdanPropertyT
    (LiteralBaseSOS.base_hasKazhdanPropertyT_of_isRationalCertificate hcert)

end LiteralKazhdanCompression
end GroupApproximation
