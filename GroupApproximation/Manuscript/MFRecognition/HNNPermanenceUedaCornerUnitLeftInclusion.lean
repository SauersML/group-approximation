import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerUnitLeft
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerMatrixIdentity

/-! # The left amalgam inclusion identifies `(1,0)` with the corner unit -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem amalgamLeftInclusion_one_zero_eq_matrixUnitLeft
    (data : CoronaConjugator G S T phi A X) :
    amalgamLeft data (amalgamLeftInclusion data
        ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data))) =
      matrixUnitLeft data 0 0 := by
  exact congrArg (amalgamLeft data)
    (amalgamLeftInclusion_one_zero_eq_matrixUnit data)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
