import GroupApproximation.Kazhdan.LiteralBaseSOS
import GroupApproximation.Monsters.AffineSL3Doubling
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.MarkedCompressionSequentialKill
import GroupApproximation.Sofic.NormMFPrintedConsequences

/-!
# The literal presentation as marked Kazhdan-compression data

This file connects the manuscript's literal eight-generator presentation to
the general analytic obstruction.  Every group-theoretic field is discharged
from the displayed relators.  The only input left explicit is property `(T)`
of the abstract group presented by the literal twenty relators; alternatively, an exact rational
sum-of-squares certificate supplies that input through `LiteralBaseSOS`.

This distinction is load-bearing.  Verifying the relators in the concrete
group `ℤ³ ⋊ SL₃(ℤ)` produces a quotient of this presented group, and
property `(T)` does not transfer backwards from that quotient.  A route via
the classical affine group therefore also needs a proved isomorphism (that
is, completeness of the printed presentation).  The theorem
`not_isOperatorMF_of_base_equiv_affine` records those two inputs separately.

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

/-- The precise presentation-completeness route to the conditional endpoint.
Property `(T)` of the concrete affine group is useful only after an
isomorphism from the literal presented base has been supplied. -/
theorem not_isOperatorMF_of_base_equiv_affine
    (e : Base ≃* AffineSL3Doubling.Gamma)
    (hT : HasKazhdanPropertyT.{0, 0} AffineSL3Doubling.Gamma) :
    ¬ IsOperatorMF MarkedGroup :=
  not_isOperatorMF_of_hasKazhdanPropertyT
    (HasKazhdanPropertyT.of_mulEquiv e hT)

/-- Conditional form of the manuscript's no-faithful-target consequence:
the literal group cannot inject into any operator-MF group. -/
theorem not_injective_to_isOperatorMF_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base)
    {H : Type*} [Group H] (hH : IsOperatorMF H)
    (f : MarkedGroup →* H) :
    ¬ Function.Injective f := by
  apply not_injective_to_isOperatorMF
    ((mark_normMFInvisible_of_hasKazhdanPropertyT hT).toCoronaMFInvisible)
    LiteralNonMFLinearWitness.literal_mark_ne_one hH f

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

/-- The proof-carrying rational-certificate form of the no-faithful-target
consequence. -/
theorem not_injective_to_isOperatorMF_of_isRationalCertificate
    {c : ℚ} (hcert : LiteralBaseSOS.IsRationalCertificate c)
    {H : Type*} [Group H] (hH : IsOperatorMF H)
    (f : MarkedGroup →* H) :
    ¬ Function.Injective f :=
  not_injective_to_isOperatorMF_of_hasKazhdanPropertyT
    (LiteralBaseSOS.base_hasKazhdanPropertyT_of_isRationalCertificate hcert)
    hH f

/-! ## The affine--Clifford witness inherits the marked obstruction -/

/-- The distinguished Clifford sign in the explicit witness is MF-invisible.
This is the functorial marked-radical step in manuscript Proposition
`prop:W`. -/
theorem witness_sign_normMFInvisible_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    NormMFInvisible
      (MarkedCompression.signAmbient LiteralNonMFLinearWitness.alpha
        ExplicitLinearModel.conjD_injective) := by
  have hmap :=
    (mark_normMFInvisible_of_hasKazhdanPropertyT hT).map
      LiteralNonMFLinearWitness.witnessHom
  simpa using hmap

/-- Consequently the explicit affine--Clifford witness group is not
operator-MF. -/
theorem witness_not_isOperatorMF_of_hasKazhdanPropertyT
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ IsOperatorMF LiteralNonMFLinearWitness.WitnessGroup := by
  intro hMF
  exact not_injective_to_isOperatorMF
    ((witness_sign_normMFInvisible_of_hasKazhdanPropertyT hT).toCoronaMFInvisible)
    (MarkedCompression.signAmbient_ne_one
      LiteralNonMFLinearWitness.alpha ExplicitLinearModel.conjD_injective)
    hMF (MonoidHom.id LiteralNonMFLinearWitness.WitnessGroup)
    Function.injective_id

/-- The same witness conclusion from an exact rational SOS certificate for
the literal base. -/
theorem witness_not_isOperatorMF_of_isRationalCertificate {c : ℚ}
    (hcert : LiteralBaseSOS.IsRationalCertificate c) :
    ¬ IsOperatorMF LiteralNonMFLinearWitness.WitnessGroup :=
  witness_not_isOperatorMF_of_hasKazhdanPropertyT
    (LiteralBaseSOS.base_hasKazhdanPropertyT_of_isRationalCertificate hcert)

end LiteralKazhdanCompression
end GroupApproximation
