import GroupApproximation.Analysis.CStarCornerMap
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedAmalgamProperties
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerWord

/-! # Restricting an evaluated Ueda amalgam map to its corner -/

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

/-- `R.base` carries the upper-left matrix unit to the upper-left matrix unit.
This is `map_one` on the entry, not a reduction, which is why the corner-unit
identity below cannot be closed by `rfl`. -/
theorem matrixTwoMap_matrixUnitZeroZero_one (R : HNNCoordinate data) :
    matrixTwoMap R.base (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data)) =
      cStarMatrixUnitTwo 0 0 (1 : R.carrier) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cStarMatrixUnitTwo]
  exact R.base.map_one'

@[simp] theorem evaluatedAmalgamMap_cornerUnit (R : HNNCoordinate data) :
    evaluatedAmalgamMap data R (cornerUnit data) =
      (cStarUpperLeftCornerUnit :
        CStarMatrix (Fin 2) (Fin 2) R.carrier) := by
  show evaluatedAmalgamMap data R
      (amalgamLeft data (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data))) =
    cStarMatrixUnitTwo 0 0 (1 : R.carrier)
  rw [evaluatedAmalgamMap_left]
  exact matrixTwoMap_matrixUnitZeroZero_one data R

/-- The entry algebra is pinned on all three corner arguments: left implicit,
`K` is a metavariable when `CStarCorner` elaborates, and the two candidate
`Mul` instances on `CStarMatrix` cannot be compared over an unknown carrier. -/
def evaluatedCornerMap (R : HNNCoordinate data) :
    CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data) →⋆ₐ[ℂ]
      CStarCorner (cStarUpperLeftCornerUnit (K := R.carrier))
        (cStarUpperLeftCornerUnit_star (K := R.carrier))
        (cStarUpperLeftCornerUnit_mul (K := R.carrier)) :=
  CStarCorner.map (evaluatedAmalgamMap data R)
    (evaluatedAmalgamMap_cornerUnit data R)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
