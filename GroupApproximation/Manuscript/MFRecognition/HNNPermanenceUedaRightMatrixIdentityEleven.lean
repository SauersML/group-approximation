import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaBasicMaps

/-! # The finite right-factor `(0,1)` matrix identity -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

theorem amalgamRightInclusion_zero_one_eq_matrixUnit
    (data : CoronaConjugator G S T phi A X) :
    amalgamRightInclusion data
        ((0 : sourceEdgeAlgebra data), (1 : targetEdgeAlgebra data)) =
      cStarMatrixUnitTwo 1 1 (1 : sourceEdgeAlgebra data) := by
  change cStarDiagonalTwo (0 : sourceEdgeAlgebra data)
      ((edgeIsomorphism data).symm (1 : targetEdgeAlgebra data)) =
    cStarMatrixUnitTwo 1 1 (1 : sourceEdgeAlgebra data)
  rw [map_one]
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
