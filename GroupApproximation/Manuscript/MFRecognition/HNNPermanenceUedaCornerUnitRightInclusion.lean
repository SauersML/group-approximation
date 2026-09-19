import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaMatrixUnitRight
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaRightMatrixIdentity

/-! # The right inclusion of `(1,0)` is its zero-zero matrix unit -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem amalgamRightInclusion_one_zero_eq_matrixUnitRight
    (data : CoronaConjugator G S T phi A X) :
    amalgamRight data (amalgamRightInclusion data
        ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data))) =
      matrixUnitRight data 0 0 := by
  unfold matrixUnitRight
  rw [amalgamRightInclusion_one_zero_eq_matrixUnit]

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
