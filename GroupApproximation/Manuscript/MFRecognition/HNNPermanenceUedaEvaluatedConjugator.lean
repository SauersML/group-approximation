import GroupApproximation.Analysis.CStarMatrixTwoCorner
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaOperations

/-! # The diagonal conjugator in an evaluated Ueda representation -/

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

abbrev HNNCoordinate := CStarHNNRepresentation
  (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data)

/-- `diag(1,R.stable)` in the two-by-two algebra of a covariant coordinate. -/
def evaluatedConjugatorMatrix (R : HNNCoordinate data) :
    unitary (CStarMatrix (Fin 2) (Fin 2) R.carrier) :=
  ⟨cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier), by
    constructor
    · rw [star_cStarDiagonalTwo, cStarDiagonalTwo_mul, star_one, one_mul,
        R.stable.property.1, cStarDiagonalTwo_one]
    · rw [star_cStarDiagonalTwo, cStarDiagonalTwo_mul, star_one, mul_one,
        R.stable.property.2, cStarDiagonalTwo_one]⟩

@[simp] theorem coe_evaluatedConjugatorMatrix (R : HNNCoordinate data) :
    ((evaluatedConjugatorMatrix data R :
        unitary (CStarMatrix (Fin 2) (Fin 2) R.carrier)) :
      CStarMatrix (Fin 2) (Fin 2) R.carrier) =
      cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier) :=
  rfl

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
