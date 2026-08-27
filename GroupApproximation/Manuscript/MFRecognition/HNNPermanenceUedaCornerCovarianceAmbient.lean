import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerCommonImages
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaMatrixIdentities

/-! # Ambient form of Ueda's corner covariance

Every proof below keeps two layers apart on purpose.  The two-by-two identity
is proved, or quoted, at an *abstract* entry algebra, where the landed
`CStarMatrixTwo` and `HNNPermanenceUedaMatrixIdentities` lemmas match
syntactically; it is then carried across a factor map by `map_star` / `map_mul`
and `congrArg`, and applied with `exact`.

Rewriting through `map_star` or `map_mul` directly does not work at the
concrete algebras of a `CoronaConjugator`: the `star` and `*` that those
lemmas produce are instantiated from the homomorphism's own structure, not
from `CStarMatrix`'s `StarRing` and `Semiring`, so the next rewrite in the
chain has no syntactic occurrence to act on.  The two spellings are
definitionally equal, which is exactly what `exact` accepts and `rw` does not.

Every `map_*` below is given its arguments explicitly.  Left as `_` they are
metavariables that the surrounding `.trans` has to solve through those same
instance paths, and an unsolved one is reported as a type mismatch in the
*statement* rather than in the proof. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The star of a unit matrix unit, at an abstract entry algebra. -/
theorem star_matrixUnitOne_ambient {K : Type} [CStarAlgebra K] (i j : Fin 2) :
    star (cStarMatrixUnitTwo i j (1 : K)) = cStarMatrixUnitTwo j i (1 : K) := by
  rw [star_cStarMatrixUnitTwo, star_one]

@[simp] theorem star_matrixUnitLeft
    (data : CoronaConjugator G S T phi A X) (i j : Fin 2) :
    star (matrixUnitLeft data i j) = matrixUnitLeft data j i := by
  show star (amalgamLeft data (cStarMatrixUnitTwo i j (1 : baseAlgebra data))) =
    amalgamLeft data (cStarMatrixUnitTwo j i (1 : baseAlgebra data))
  exact (map_star (amalgamLeft data)
      (cStarMatrixUnitTwo i j (1 : baseAlgebra data))).symm.trans
    (congrArg (amalgamLeft data) (star_matrixUnitOne_ambient i j))

@[simp] theorem star_matrixUnitRight
    (data : CoronaConjugator G S T phi A X) (i j : Fin 2) :
    star (matrixUnitRight data i j) = matrixUnitRight data j i := by
  show star (amalgamRight data
      (cStarMatrixUnitTwo i j (1 : sourceEdgeAlgebra data))) =
    amalgamRight data (cStarMatrixUnitTwo j i (1 : sourceEdgeAlgebra data))
  exact (map_star (amalgamRight data)
      (cStarMatrixUnitTwo i j (1 : sourceEdgeAlgebra data))).symm.trans
    (congrArg (amalgamRight data) (star_matrixUnitOne_ambient i j))

theorem matrixUnitRight_source_sandwich
    (data : CoronaConjugator G S T phi A X) (b : sourceEdgeAlgebra data) :
    matrixUnitRight data 1 0 *
        amalgamRight data (cStarDiagonalTwo b 0) *
      matrixUnitRight data 0 1 =
        amalgamRight data (cStarDiagonalTwo 0 b) := by
  show amalgamRight data (cStarMatrixUnitTwo 1 0 (1 : sourceEdgeAlgebra data)) *
      amalgamRight data (cStarDiagonalTwo b 0) *
      amalgamRight data (cStarMatrixUnitTwo 0 1 (1 : sourceEdgeAlgebra data)) =
    amalgamRight data (cStarDiagonalTwo 0 b)
  have hstep :
      amalgamRight data (cStarMatrixUnitTwo 1 0 (1 : sourceEdgeAlgebra data)) *
          amalgamRight data (cStarDiagonalTwo b 0) =
        amalgamRight data
          (cStarMatrixUnitTwo 1 0 (1 : sourceEdgeAlgebra data) *
            cStarDiagonalTwo b 0) :=
    (map_mul (amalgamRight data)
      (cStarMatrixUnitTwo 1 0 (1 : sourceEdgeAlgebra data))
      (cStarDiagonalTwo b 0)).symm
  rw [hstep]
  exact (map_mul (amalgamRight data)
        (cStarMatrixUnitTwo 1 0 (1 : sourceEdgeAlgebra data) *
          cStarDiagonalTwo b 0)
        (cStarMatrixUnitTwo 0 1 (1 : sourceEdgeAlgebra data))).symm.trans
    (congrArg (amalgamRight data) (matrixUnit_ten_diagonal_zero_zeroOne b))

theorem matrixUnitLeft_target_sandwich
    (data : CoronaConjugator G S T phi A X) (c : targetEdgeAlgebra data) :
    matrixUnitLeft data 0 1 *
        amalgamLeft data
          (cStarDiagonalTwo 0 (c : baseAlgebra data)) *
      matrixUnitLeft data 1 0 =
        amalgamLeft data
          (cStarDiagonalTwo (c : baseAlgebra data) 0) := by
  show amalgamLeft data (cStarMatrixUnitTwo 0 1 (1 : baseAlgebra data)) *
      amalgamLeft data (cStarDiagonalTwo 0 (c : baseAlgebra data)) *
      amalgamLeft data (cStarMatrixUnitTwo 1 0 (1 : baseAlgebra data)) =
    amalgamLeft data (cStarDiagonalTwo (c : baseAlgebra data) 0)
  have hstep :
      amalgamLeft data (cStarMatrixUnitTwo 0 1 (1 : baseAlgebra data)) *
          amalgamLeft data (cStarDiagonalTwo 0 (c : baseAlgebra data)) =
        amalgamLeft data
          (cStarMatrixUnitTwo 0 1 (1 : baseAlgebra data) *
            cStarDiagonalTwo 0 (c : baseAlgebra data)) :=
    (map_mul (amalgamLeft data)
      (cStarMatrixUnitTwo 0 1 (1 : baseAlgebra data))
      (cStarDiagonalTwo 0 (c : baseAlgebra data))).symm
  rw [hstep]
  exact (map_mul (amalgamLeft data)
        (cStarMatrixUnitTwo 0 1 (1 : baseAlgebra data) *
          cStarDiagonalTwo 0 (c : baseAlgebra data))
        (cStarMatrixUnitTwo 1 0 (1 : baseAlgebra data))).symm.trans
    (congrArg (amalgamLeft data)
      (matrixUnit_zeroOne_zeroDiagonal_ten (c : baseAlgebra data)))

theorem cornerWord_covariance_ambient
    (data : CoronaConjugator G S T phi A X) (b : sourceEdgeAlgebra data) :
    (matrixUnitLeft data 0 1 * matrixUnitRight data 1 0) *
        amalgamLeft data (cStarDiagonalTwo (b : baseAlgebra data) 0) *
      star (matrixUnitLeft data 0 1 * matrixUnitRight data 1 0) =
        amalgamLeft data
          (cStarDiagonalTwo
            ((edgeIsomorphism data b : targetEdgeAlgebra data) :
              baseAlgebra data) 0) := by
  rw [star_mul, star_matrixUnitRight, star_matrixUnitLeft,
    amalgam_diagonal_source_zero_common]
  calc
    (matrixUnitLeft data 0 1 * matrixUnitRight data 1 0) *
          amalgamRight data (cStarDiagonalTwo b 0) *
        (matrixUnitRight data 0 1 * matrixUnitLeft data 1 0) =
      matrixUnitLeft data 0 1 *
          (matrixUnitRight data 1 0 *
            amalgamRight data (cStarDiagonalTwo b 0) *
              matrixUnitRight data 0 1) *
        matrixUnitLeft data 1 0 := by simp only [mul_assoc]
    _ = matrixUnitLeft data 0 1 *
          amalgamRight data (cStarDiagonalTwo 0 b) *
        matrixUnitLeft data 1 0 := by
      rw [matrixUnitRight_source_sandwich]
    _ = matrixUnitLeft data 0 1 *
          amalgamLeft data
            (cStarDiagonalTwo 0
              ((edgeIsomorphism data b : targetEdgeAlgebra data) :
                baseAlgebra data)) *
        matrixUnitLeft data 1 0 := by
      rw [amalgam_zero_diagonal_edge_common]
    _ = amalgamLeft data
          (cStarDiagonalTwo
            ((edgeIsomorphism data b : targetEdgeAlgebra data) :
              baseAlgebra data) 0) :=
      matrixUnitLeft_target_sandwich data (edgeIsomorphism data b)

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
