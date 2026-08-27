import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaUniversalMapProperties
import GroupApproximation.Meta.AxiomGuard

/-!
# A direct faithful Ueda corner map

For each covariant representation `R` of the universal HNN datum, the Ueda
amalgam has a compatible two-by-two representation on `M₂(R.carrier)`.
Restricted to Ueda's corner, its upper-left entry is evaluation at `R` after
composition with the canonical HNN map.  Joint faithfulness of the coordinate
evaluations therefore proves that the HNN-to-corner map is injective.
-/

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
      cStarDiagonalTwo (1 : R.carrier) (R.stable : R.carrier) := rfl

def evaluatedFactorLeft (R : HNNCoordinate data) :
    matrixBaseAlgebra data →⋆ₐ[ℂ]
      CStarMatrix (Fin 2) (Fin 2) R.carrier :=
  matrixTwoMap R.base

def evaluatedFactorRight (R : HNNCoordinate data) :
    matrixEdgeAlgebra data →⋆ₐ[ℂ]
      CStarMatrix (Fin 2) (Fin 2) R.carrier :=
  (Unitary.conjStarAlgAut ℂ (CStarMatrix (Fin 2) (Fin 2) R.carrier)
      (evaluatedConjugatorMatrix data R)).toStarAlgHom.comp
    (matrixTwoMap (R.base.comp (sourceEdgeAlgebra data).subtype))

theorem evaluated_covariance_conj (R : HNNCoordinate data)
    (b : sourceEdgeAlgebra data) :
    (R.stable : R.carrier) * R.base (b : baseAlgebra data) *
        star (R.stable : R.carrier) =
      R.base (((edgeIsomorphism data b : targetEdgeAlgebra data) :
        baseAlgebra data)) := by
  calc
    (R.stable : R.carrier) * R.base (b : baseAlgebra data) *
        star (R.stable : R.carrier) =
      (R.base (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) * (R.stable : R.carrier)) *
        star (R.stable : R.carrier) := by rw [R.covariance b]
    _ = R.base (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) *
        ((R.stable : R.carrier) * star (R.stable : R.carrier)) := by
      rw [mul_assoc]
    _ = R.base (((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) := by rw [R.stable.property.1, mul_one]

theorem evaluatedFactor_compatible_apply (R : HNNCoordinate data)
    (c : edgeSumAlgebra data) :
    evaluatedFactorRight data R (amalgamRightInclusion data c) =
      evaluatedFactorLeft data R (amalgamLeftInclusion data c) := by
  have hconj := evaluated_covariance_conj data R
    ((edgeIsomorphism data).symm c.2)
  rw [StarAlgEquiv.apply_symm_apply] at hconj
  change cStarDiagonalTwo (R.base (c.1 : baseAlgebra data))
      ((R.stable : R.carrier) *
        R.base ((((edgeIsomorphism data).symm c.2 : sourceEdgeAlgebra data) :
          baseAlgebra data)) * star (R.stable : R.carrier)) =
    cStarDiagonalTwo (R.base (c.1 : baseAlgebra data))
      (R.base (c.2 : baseAlgebra data))
  rw [hconj]

theorem evaluatedFactor_compatible (R : HNNCoordinate data) :
    (evaluatedFactorLeft data R).comp (amalgamLeftInclusion data) =
      (evaluatedFactorRight data R).comp (amalgamRightInclusion data) := by
  apply StarAlgHom.ext
  intro c
  exact (evaluatedFactor_compatible_apply data R c).symm

def evaluatedAmalgamRepresentation (R : HNNCoordinate data) :
    CStarAmalgamRepresentation
      (amalgamLeftInclusion data) (amalgamRightInclusion data) :=
  CStarAmalgamRepresentation.ofCompatiblePair
    (amalgamLeftInclusion data) (amalgamRightInclusion data)
    (evaluatedFactorLeft data R) (evaluatedFactorRight data R)
    (evaluatedFactor_compatible data R)

def evaluatedAmalgamMap (R : HNNCoordinate data) :
    amalgam data →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) R.carrier :=
  universalCStarAmalgamEval
    (amalgamLeftInclusion data) (amalgamRightInclusion data)
    (evaluatedAmalgamRepresentation data R)

@[simp] theorem evaluatedAmalgamMap_left (R : HNNCoordinate data)
    (M : matrixBaseAlgebra data) :
    evaluatedAmalgamMap data R (amalgamLeft data M) =
      evaluatedFactorLeft data R M := rfl

@[simp] theorem evaluatedAmalgamMap_right (R : HNNCoordinate data)
    (M : matrixEdgeAlgebra data) :
    evaluatedAmalgamMap data R (amalgamRight data M) =
      evaluatedFactorRight data R M := rfl

@[simp] theorem evaluatedAmalgamMap_cornerUnit (R : HNNCoordinate data) :
    evaluatedAmalgamMap data R (cornerUnit data) =
      cStarMatrixUnitTwo 0 0 (1 : R.carrier) := by
  rw [cornerUnit_eq_matrixUnitLeft]
  rfl

theorem evaluatedCornerMatrix_eq (R : HNNCoordinate data)
    (x : CStarCorner (cornerUnit data) (cornerUnit_star data)
      (cornerUnit_mul data)) :
    evaluatedAmalgamMap data R (x : amalgam data) =
      cStarMatrixUnitTwo 0 0
        (evaluatedAmalgamMap data R (x : amalgam data) 0 0) := by
  have hl := congrArg (evaluatedAmalgamMap data R) x.property.1
  have hr := congrArg (evaluatedAmalgamMap data R) x.property.2
  rw [map_mul, evaluatedAmalgamMap_cornerUnit] at hl hr
  ext i j
  fin_cases i <;> fin_cases j
  · simp
  · have h := congrArg
      (fun M : CStarMatrix (Fin 2) (Fin 2) R.carrier ↦ M 0 1) hr
    simpa [CStarExactness.cstarMatrix_mul_apply, cStarMatrixUnitTwo] using h
  · have h := congrArg
      (fun M : CStarMatrix (Fin 2) (Fin 2) R.carrier ↦ M 1 0) hl
    simpa [CStarExactness.cstarMatrix_mul_apply, cStarMatrixUnitTwo] using h
  · have h := congrArg
      (fun M : CStarMatrix (Fin 2) (Fin 2) R.carrier ↦ M 1 1) hl
    simpa [CStarExactness.cstarMatrix_mul_apply, cStarMatrixUnitTwo] using h

def evaluatedCornerMap (R : HNNCoordinate data) :
    CStarCorner (cornerUnit data) (cornerUnit_star data)
        (cornerUnit_mul data) →⋆ₐ[ℂ] R.carrier where
  toFun x := evaluatedAmalgamMap data R (x : amalgam data) 0 0
  map_one' := by
    change evaluatedAmalgamMap data R (cornerUnit data) 0 0 = 1
    rw [evaluatedAmalgamMap_cornerUnit]
    simp
  map_mul' x y := by
    have hx := evaluatedCornerMatrix_eq data R x
    have hy := evaluatedCornerMatrix_eq data R y
    change evaluatedAmalgamMap data R ((x : amalgam data) * y) 0 0 = _
    rw [map_mul, hx, hy, cStarMatrixUnitTwo_mul]
    simp
  map_zero' := by simp
  map_add' x y := by
    change evaluatedAmalgamMap data R ((x : amalgam data) + y) 0 0 = _
    rw [map_add]
    rfl
  commutes' r := by
    change evaluatedAmalgamMap data R
      ((algebraMap ℂ
        (CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) r :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) : amalgam data) 0 0 =
      algebraMap ℂ R.carrier r
    rw [Algebra.algebraMap_eq_smul_one]
    change evaluatedAmalgamMap data R (r • cornerUnit data) 0 0 = _
    rw [map_smul, evaluatedAmalgamMap_cornerUnit]
    simp [CStarMatrix.algebraMap_apply]
  map_star' x := by
    change evaluatedAmalgamMap data R (star (x : amalgam data)) 0 0 =
      star (evaluatedAmalgamMap data R (x : amalgam data) 0 0)
    rw [map_star, CStarMatrix.star_apply]

@[simp] theorem evaluatedCornerMap_base (R : HNNCoordinate data)
    (d : baseAlgebra data) :
    evaluatedCornerMap data R (cornerBaseMap data d) = R.base d := by
  change matrixTwoMap R.base (cStarDiagonalTwo d 0) 0 0 = R.base d
  rw [matrixTwoMap_diagonal]
  simp

@[simp] theorem evaluatedCornerMap_stable (R : HNNCoordinate data) :
    evaluatedCornerMap data R (cornerStableUnitary data) =
      (R.stable : R.carrier) := by
  change evaluatedAmalgamMap data R
      (((cornerStableUnitary data : unitary
          (CStarCorner (cornerUnit data) (cornerUnit_star data)
            (cornerUnit_mul data))) :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) : amalgam data) 0 0 =
    (R.stable : R.carrier)
  rw [coe_cornerStableUnitary, map_mul,
    show evaluatedAmalgamMap data R (matrixUnitLeft data 0 1) =
      cStarMatrixUnitTwo 0 1 (1 : R.carrier) by rfl]
  change (cStarMatrixUnitTwo 0 1 (1 : R.carrier) *
      ((evaluatedConjugatorMatrix data R :
          CStarMatrix (Fin 2) (Fin 2) R.carrier) *
        cStarMatrixUnitTwo 1 0 (1 : R.carrier) *
        star (evaluatedConjugatorMatrix data R :
          CStarMatrix (Fin 2) (Fin 2) R.carrier))) 0 0 = _
  rw [coe_evaluatedConjugatorMatrix, star_cStarDiagonalTwo,
    cStarDiagonalTwo_mul_unit, cStarMatrixUnitTwo_mul_diagonal,
    cStarMatrixUnitTwo_mul, cStarMatrixUnitTwo_mul]
  simp

theorem evaluatedCornerMap_comp_uedaCornerMap (R : HNNCoordinate data) :
    (evaluatedCornerMap data R).comp (uedaCornerMap data) =
      universalCStarHNNEval (sourceEdgeAlgebra data)
        (targetEdgeAlgebra data) (edgeIsomorphism data) R := by
  apply (universalCStarHNN_existsUnique_lift
    (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data)
    R.base R.stable R.covariance).unique
  constructor
  · intro d
    simp [evaluatedCornerMap_base]
  · simp [evaluatedCornerMap_stable]

theorem uedaCornerMap_injective : Function.Injective (uedaCornerMap data) := by
  intro x y hxy
  apply universalCStarHNN_eq_of_forall_eval_eq
  intro R
  have h := congrArg (evaluatedCornerMap data R) hxy
  change ((evaluatedCornerMap data R).comp (uedaCornerMap data)) x =
    ((evaluatedCornerMap data R).comp (uedaCornerMap data)) y at h
  rw [evaluatedCornerMap_comp_uedaCornerMap data R] at h
  exact h

/-- Closed endpoint for the direct Ueda corner embedding. -/
def DirectUedaCornerEmbedding : Prop :=
  ∀ {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
    {A : Type} [CStarAlgebra A]
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (data : CoronaConjugator G S T phi A X),
      Function.Injective (uedaCornerMap data)

theorem directUedaCornerEmbedding : DirectUedaCornerEmbedding := by
  intro G _ S T phi A _ X _ data
  exact uedaCornerMap_injective data

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.HNNPermanence.directUedaCornerEmbedding
