import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedAmalgamMap

/-! # The evaluated amalgam map on the two universal factors -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open scoped CStarAlgebra Matrix

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

@[simp] theorem evaluatedAmalgamMap_left (R : HNNCoordinate data)
    (M : matrixBaseAlgebra data) :
    evaluatedAmalgamMap data R (amalgamLeft data M) =
      evaluatedFactorLeft data R M :=
  rfl

@[simp] theorem evaluatedAmalgamMap_right (R : HNNCoordinate data)
    (M : matrixEdgeAlgebra data) :
    evaluatedAmalgamMap data R (amalgamRight data M) =
      evaluatedFactorRight data R M :=
  rfl

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
