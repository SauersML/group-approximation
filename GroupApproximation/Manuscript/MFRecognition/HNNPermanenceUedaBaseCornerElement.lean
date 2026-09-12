import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerWord

/-!
# The canonical base map into Ueda's corner

This is the first unconditional half of the Ueda corner construction: the
map `d ↦ diag(d,0)` from the HNN base algebra into the corner `ePe`.

The two support identities are proved at an abstract entry algebra, where the
landed `CStarMatrixTwo` lemmas match syntactically, and are then carried
across the left factor map with `map_mul` and `congrArg`.  The membership
itself is stated with `change`: `cornerUnit data` is by definition
`amalgamLeft data (e₀₀)`, so no rewrite of the idempotent is needed -- and
none is possible, because the ambient membership predicate carries the
self-adjointness proof of that same idempotent as an argument.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- `e₀₀ · diag(d,0) = diag(d,0)`. -/
theorem matrixUnitZeroZero_mul_diagonalZero {K : Type} [CStarAlgebra K]
    (d : K) :
    cStarMatrixUnitTwo 0 0 (1 : K) * cStarDiagonalTwo d 0 =
      cStarDiagonalTwo d 0 := by
  rw [cStarMatrixUnitTwo_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cStarDiagonalTwo, cStarMatrixUnitTwo]

/-- `diag(d,0) · e₀₀ = diag(d,0)`. -/
theorem diagonalZero_mul_matrixUnitZeroZero {K : Type} [CStarAlgebra K]
    (d : K) :
    cStarDiagonalTwo d 0 * cStarMatrixUnitTwo 0 0 (1 : K) =
      cStarDiagonalTwo d 0 := by
  rw [cStarDiagonalTwo_mul_unit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cStarDiagonalTwo, cStarMatrixUnitTwo]

theorem amalgamLeft_diagonal_zero_mem_corner
    (data : CoronaConjugator G S T phi A X) (d : baseAlgebra data) :
    amalgamLeft data (cStarDiagonalTwo d 0) ∈
      cStarCornerSubalgebra (cornerUnit data) (cornerUnit_star data) := by
  constructor
  · change amalgamLeft data (cStarMatrixUnitTwo 0 0 1) *
        amalgamLeft data (cStarDiagonalTwo d 0) =
      amalgamLeft data (cStarDiagonalTwo d 0)
    exact (map_mul (amalgamLeft data) _ _).symm.trans
      (congrArg (amalgamLeft data) (matrixUnitZeroZero_mul_diagonalZero d))
  · change amalgamLeft data (cStarDiagonalTwo d 0) *
        amalgamLeft data (cStarMatrixUnitTwo 0 0 1) =
      amalgamLeft data (cStarDiagonalTwo d 0)
    exact (map_mul (amalgamLeft data) _ _).symm.trans
      (congrArg (amalgamLeft data) (diagonalZero_mul_matrixUnitZeroZero d))

/-- The element `diag(d,0)` regarded as an element of `ePe`. -/
def cornerBaseElement (data : CoronaConjugator G S T phi A X)
    (d : baseAlgebra data) :
    CStarCorner (cornerUnit data) (cornerUnit_star data)
      (cornerUnit_mul data) :=
  ⟨amalgamLeft data (cStarDiagonalTwo d 0),
    amalgamLeft_diagonal_zero_mem_corner data d⟩

@[simp] theorem coe_cornerBaseElement
    (data : CoronaConjugator G S T phi A X) (d : baseAlgebra data) :
    ((cornerBaseElement data d :
      CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data)) : amalgam data) =
      amalgamLeft data (cStarDiagonalTwo d 0) :=
  rfl

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
