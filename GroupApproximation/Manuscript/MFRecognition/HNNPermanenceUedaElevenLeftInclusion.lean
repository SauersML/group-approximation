import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaMatrixUnitLeft
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaLeftMatrixIdentityEleven

/-! # The left `(0,1)` inclusion gives the one-one matrix unit -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem amalgamLeftInclusion_zero_one_eq_matrixUnitLeft
    (data : CoronaConjugator G S T phi A X) :
    amalgamLeft data (amalgamLeftInclusion data
        ((0 : sourceEdgeAlgebra data), (1 : targetEdgeAlgebra data))) =
      matrixUnitLeft data 1 1 := by
  change amalgamLeft data (amalgamLeftInclusion data
      ((0 : sourceEdgeAlgebra data), (1 : targetEdgeAlgebra data))) =
    amalgamLeft data (cStarMatrixUnitTwo 1 1 (1 : baseAlgebra data))
  exact congrArg (amalgamLeft data)
    (amalgamLeftInclusion_zero_one_eq_matrixUnit data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
