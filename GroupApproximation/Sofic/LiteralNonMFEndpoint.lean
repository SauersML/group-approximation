import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import GroupApproximation.Sofic.MarkedCompressionSequentialKill

/-!
# Conditional analytic endpoints for the literal eight-generator group

The literal presentation and its exact separating Clifford realization are
proved in `LiteralNonMFPresentation` and `LiteralNonMFLinearWitness`.  The
only remaining input for the analytic obstruction is Kazhdan property `(T)`
for the literal six-generator base.  Every theorem in this file therefore
takes that input explicitly; no presentation-completeness or property-`(T)`
claim is hidden in the endpoint packaging.
-/

namespace GroupApproximation
namespace LiteralNonMFEndpoint

open LiteralNonMFPresentation LiteralNonMFLinearWitness

/-- Conditional on property `(T)` for the literal base, the marked word is
killed by every homomorphism to every operator-norm matrix ultraproduct. -/
theorem literal_mark_normMFInvisible
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    NormMFInvisible mark := by
  rw [← inclusionData_word hT]
  exact (inclusionData hT).word_normMFInvisible

/-- Conditional on property `(T)` for the literal base, the literal
eight-generator group is not weak/operator-norm MF. -/
theorem literal_not_isWeakMF
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ IsWeakMF MarkedGroup := by
  apply (inclusionData hT).not_isWeakMF
  simpa only [inclusionData_word] using literal_mark_ne_one

/-- Conditional on property `(T)` for the literal base, the literal
eight-generator group is not MF in the standard cofinite norm-matrix-corona
sense. -/
theorem literal_not_isOperatorMF
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    ¬ IsOperatorMF MarkedGroup := by
  apply (inclusionData hT).not_isOperatorMF
  simpa only [inclusionData_word] using literal_mark_ne_one

/-- Finite-presentation package for the conditional weak-MF endpoint. -/
theorem literal_finitelyPresented_not_isWeakMF
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    Group.IsFinitelyPresented MarkedGroup ∧ ¬ IsWeakMF MarkedGroup :=
  ⟨inferInstance, literal_not_isWeakMF hT⟩

/-- Countability package for the conditional weak-MF endpoint. -/
theorem literal_countable_not_isWeakMF
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    Countable MarkedGroup ∧ ¬ IsWeakMF MarkedGroup :=
  ⟨inferInstance, literal_not_isWeakMF hT⟩

/-- Finite-presentation package for the conditional standard MF endpoint. -/
theorem literal_finitelyPresented_not_isOperatorMF
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    Group.IsFinitelyPresented MarkedGroup ∧ ¬ IsOperatorMF MarkedGroup :=
  ⟨inferInstance, literal_not_isOperatorMF hT⟩

/-- Countability package for the conditional standard MF endpoint. -/
theorem literal_countable_not_isOperatorMF
    (hT : HasKazhdanPropertyT.{0, 0} Base) :
    Countable MarkedGroup ∧ ¬ IsOperatorMF MarkedGroup :=
  ⟨inferInstance, literal_not_isOperatorMF hT⟩

end LiteralNonMFEndpoint
end GroupApproximation
