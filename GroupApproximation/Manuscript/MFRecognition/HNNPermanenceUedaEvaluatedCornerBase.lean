import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedCornerDef
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaBaseCornerMap
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaMatrixIdentities

/-! # The evaluated Ueda corner map on the base algebra -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

@[simp] theorem evaluatedCornerMap_base (R : HNNCoordinate data)
    (d : baseAlgebra data) :
    evaluatedCornerMap data R (cornerBaseMap data d) =
      cStarUpperLeftCornerMap (R.base d) := by
  apply Subtype.ext
  change matrixTwoMap R.base (cStarDiagonalTwo d 0) =
    cStarMatrixUnitTwo 0 0 (R.base d)
  rw [matrixTwoMap_diagonal, map_zero, cStarDiagonalTwo_eq_matrixUnit_zero]

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
