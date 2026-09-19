import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedCompatibility

/-! # The compatible amalgam representation attached to an HNN coordinate -/

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

def evaluatedAmalgamRepresentation (R : HNNCoordinate data) :
    CStarAmalgamRepresentation
      (amalgamLeftInclusion data) (amalgamRightInclusion data) :=
  CStarAmalgamRepresentation.ofCompatiblePair
    (amalgamLeftInclusion data) (amalgamRightInclusion data)
    (evaluatedFactorLeft data R) (evaluatedFactorRight data R)
    (evaluatedFactor_compatible data R)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
