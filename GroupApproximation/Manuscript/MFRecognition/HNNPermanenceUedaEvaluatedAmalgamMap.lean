import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamCommonImage
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedRepresentation

/-! # Evaluation of Ueda's amalgam in an HNN coordinate -/

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

def evaluatedAmalgamMap (R : HNNCoordinate data) :
    amalgam data →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) R.carrier :=
  universalCStarAmalgamEval
    (amalgamLeftInclusion data) (amalgamRightInclusion data)
    (evaluatedAmalgamRepresentation data R)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
