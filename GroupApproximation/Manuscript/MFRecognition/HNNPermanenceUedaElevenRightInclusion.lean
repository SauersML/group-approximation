import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaMatrixUnitRight
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaRightMatrixIdentityEleven

/-! # The right `(0,1)` inclusion gives the one-one matrix unit -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem amalgamRightInclusion_zero_one_eq_matrixUnitRight
    (data : CoronaConjugator G S T phi A X) :
    amalgamRight data (amalgamRightInclusion data
        ((0 : sourceEdgeAlgebra data), (1 : targetEdgeAlgebra data))) =
      matrixUnitRight data 1 1 := by
  unfold matrixUnitRight
  rw [amalgamRightInclusion_zero_one_eq_matrixUnit]

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
