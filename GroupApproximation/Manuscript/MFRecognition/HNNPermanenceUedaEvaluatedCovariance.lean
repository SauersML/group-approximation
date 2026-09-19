import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedFactorDefs

/-! # Covariance in an evaluated HNN coordinate -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

theorem evaluated_covariance_conj (R : HNNCoordinate data)
    (b : sourceEdgeAlgebra data) :
    (R.stable : R.carrier) * R.base (b : baseAlgebra data) *
        star (R.stable : R.carrier) =
      R.base (((edgeIsomorphism data b : targetEdgeAlgebra data) :
        baseAlgebra data)) := by
  calc
    (R.stable : R.carrier) * R.base (b : baseAlgebra data) *
        star (R.stable : R.carrier) =
      (R.base (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) * (R.stable : R.carrier)) *
        star (R.stable : R.carrier) := by
      exact congrArg (fun y => y * star (R.stable : R.carrier)) (R.covariance b)
    _ = R.base (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) *
        ((R.stable : R.carrier) * star (R.stable : R.carrier)) := by
      rw [mul_assoc]
    _ = R.base (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) := by rw [R.stable.property.2, mul_one]

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
