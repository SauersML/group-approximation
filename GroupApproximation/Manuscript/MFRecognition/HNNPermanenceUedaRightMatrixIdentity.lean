import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaBasicMaps

/-! # The finite right-factor matrix identity for Ueda's corner projection -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem amalgamRightInclusion_one_zero_eq_matrixUnit
    (data : CoronaConjugator G S T phi A X) :
    amalgamRightInclusion data
        ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data)) =
      cStarMatrixUnitTwo 0 0 (1 : sourceEdgeAlgebra data) := by
  change cStarDiagonalTwo (1 : sourceEdgeAlgebra data)
      ((edgeIsomorphism data).symm (0 : targetEdgeAlgebra data)) =
    cStarMatrixUnitTwo 0 0 (1 : sourceEdgeAlgebra data)
  rw [map_zero]
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cStarDiagonalTwo, cStarMatrixUnitTwo]
  all_goals rfl

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
