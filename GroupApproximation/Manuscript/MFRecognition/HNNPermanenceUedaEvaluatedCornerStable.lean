import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedCornerBase
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaUniversalMapProperties

/-! # The evaluated Ueda corner map on the stable unitary

The image of a matrix unit under an evaluated factor map is `map_one` on the
entry, not a reduction, so the two factor formulas below are proved rather than
asserted by `rfl`.  Everything else is the two-by-two computation
`e₀₁ · diag(1,s) e₁₀ diag(1,s)* = e₀₀ s`, which the landed `CStarMatrixTwo`
lemmas do in one rewrite chain once both factors are in matrix-unit form. -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open scoped CStarAlgebra Matrix

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- A unital star-algebra homomorphism carries matrix units to matrix units.
This is `map_one`/`map_zero` entrywise; at an abstract entry algebra both are
`simp` lemmas and the index case split is the whole proof. -/
theorem matrixTwoMap_matrixUnitOne {E K : Type} [CStarAlgebra E]
    [CStarAlgebra K] (f : E →⋆ₐ[ℂ] K) (i j : Fin 2) :
    matrixTwoMap f (cStarMatrixUnitTwo i j (1 : E)) =
      cStarMatrixUnitTwo i j (1 : K) := by
  ext p q
  rw [matrixTwoMap_entry, cStarMatrixUnitTwo_apply, cStarMatrixUnitTwo_apply]
  by_cases h : i = p ∧ j = q
  · rw [if_pos h, if_pos h, map_one]
  · rw [if_neg h, if_neg h, map_zero]

variable (data : CoronaConjugator G S T phi A X)

/-- The left factor sends `e_ij` to `e_ij`. -/
theorem evaluatedAmalgamMap_matrixUnitLeft (R : HNNCoordinate data)
    (i j : Fin 2) :
    evaluatedAmalgamMap data R (matrixUnitLeft data i j) =
      cStarMatrixUnitTwo i j (1 : R.carrier) := by
  show matrixTwoMap R.base (cStarMatrixUnitTwo i j (1 : baseAlgebra data)) =
    cStarMatrixUnitTwo i j (1 : R.carrier)
  exact matrixTwoMap_matrixUnitOne R.base i j

/-- The right factor sends `e_ij` to `diag(1,s) e_ij diag(1,s)*`.

Both steps are `congrArg` rather than `rw` on purpose.  Rewriting the inner
factor inside the conjugation makes the goal ill-typed at `instances`
transparency: `↥(baseAlgebra data)` reaches `Semiring`/`StarRing`/`Algebra`
two ways -- through `StarSubalgebra`/`SubringClass`, which is what naming
`(sourceEdgeAlgebra data).subtype` selects, and through
`baseAlgebraCStarAlgebra`, which is what `R.carrier` fixes -- and a motive
spanning both cannot typecheck.  Letting the inner hom be inferred from the
goal, and moving the rewriting outside the conjugation, keeps one path
throughout. -/
theorem evaluatedAmalgamMap_matrixUnitRight (R : HNNCoordinate data)
    (i j : Fin 2) :
    evaluatedAmalgamMap data R (matrixUnitRight data i j) =
      cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier) *
          cStarMatrixUnitTwo i j (1 : R.carrier) *
        star (cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier)) := by
  have hincl : matrixEdgeInclusion data
        (cStarMatrixUnitTwo i j (1 : sourceEdgeAlgebra data)) =
      cStarMatrixUnitTwo i j (1 : baseAlgebra data) :=
    matrixTwoMap_matrixUnitOne _ i j
  have hinner : matrixTwoMap R.base
        (matrixEdgeInclusion data
          (cStarMatrixUnitTwo i j (1 : sourceEdgeAlgebra data))) =
      cStarMatrixUnitTwo i j (1 : R.carrier) :=
    (congrArg (matrixTwoMap R.base) hincl).trans
      (matrixTwoMap_matrixUnitOne R.base i j)
  show cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier) *
      matrixTwoMap R.base
        (matrixEdgeInclusion data
          (cStarMatrixUnitTwo i j (1 : sourceEdgeAlgebra data))) *
      star (cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier)) = _
  exact congrArg
    (fun Y : CStarMatrix (Fin 2) (Fin 2) R.carrier =>
      cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier) * Y *
        star (cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier)))
    hinner

@[simp] theorem evaluatedCornerMap_stable (R : HNNCoordinate data) :
    evaluatedCornerMap data R (cornerStableUnitary data) =
      cStarUpperLeftCornerMap (R.stable : R.carrier) := by
  apply Subtype.ext
  change evaluatedAmalgamMap data R
      (((cornerStableUnitary data : unitary
          (CStarCorner (cornerUnit data) (cornerUnit_star data)
            (cornerUnit_mul data))) :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) : amalgam data) =
    cStarMatrixUnitTwo 0 0 (R.stable : R.carrier)
  rw [coe_cornerStableUnitary, map_mul, evaluatedAmalgamMap_matrixUnitLeft,
    evaluatedAmalgamMap_matrixUnitRight, star_cStarDiagonalTwo,
    cStarDiagonalTwo_mul_unit, cStarMatrixUnitTwo_mul_diagonal,
    cStarMatrixUnitTwo_mul]
  simp

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
