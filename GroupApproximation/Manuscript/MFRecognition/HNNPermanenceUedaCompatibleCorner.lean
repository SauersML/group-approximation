import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaBaseCornerMap
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaMatrixIdentities
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUniversalDef
import GroupApproximation.Meta.AxiomGuard

/-!
# The Ueda corner over an explicit compatible coordinate

This file deliberately takes the two factor maps and their compatibility as
explicit arguments.  This avoids unfolding the instance-indexed
`CStarAmalgamRepresentation` bundle after the product and matrix C-star
instances have been installed.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNAmalgamCornerSentences
open scoped CStarAlgebra Matrix

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
variable (data : CoronaConjugator G S T phi A X)
variable {E : Type} [CStarAlgebra E] [Nontrivial E]
variable (left : matrixBaseAlgebra data →⋆ₐ[ℂ] E)
variable (right : matrixEdgeAlgebra data →⋆ₐ[ℂ] E)
variable (compatible : left.comp (amalgamLeftInclusion data) =
  right.comp (amalgamRightInclusion data))

def compatibleMatrixUnitLeft (i j : Fin 2) : E :=
  left (cStarMatrixUnitTwo i j (1 : baseAlgebra data))

def compatibleMatrixUnitRight (i j : Fin 2) : E :=
  right (cStarMatrixUnitTwo i j (1 : sourceEdgeAlgebra data))

def compatibleCornerUnit : E := compatibleMatrixUnitLeft data left 0 0

theorem compatible_matrixUnitOne_star {K : Type} [CStarAlgebra K]
    (i j : Fin 2) :
    star (cStarMatrixUnitTwo i j (1 : K)) =
      cStarMatrixUnitTwo j i (1 : K) := by
  rw [star_cStarMatrixUnitTwo, star_one]

theorem compatible_matrixUnitOne_mul {K : Type} [CStarAlgebra K]
    (i j l : Fin 2) :
    cStarMatrixUnitTwo i j (1 : K) * cStarMatrixUnitTwo j l (1 : K) =
      cStarMatrixUnitTwo i l (1 : K) := by
  rw [cStarMatrixUnitTwo_mul]
  simp

/-- The two diagonal matrix units add up to the unit of `M₂`. -/
theorem compatible_matrixUnitOne_add {K : Type} [CStarAlgebra K] :
    cStarMatrixUnitTwo 0 0 (1 : K) + cStarMatrixUnitTwo 1 1 (1 : K) = 1 := by
  rw [← cStarDiagonalTwo_one_zero, ← cStarDiagonalTwo_zero_one,
    ← cStarDiagonalTwo_one (K := K)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [Nontrivial E] in
theorem compatibleCornerUnit_star :
    star (compatibleCornerUnit data left) = compatibleCornerUnit data left := by
  exact (map_star left _).symm.trans
    (congrArg left (compatible_matrixUnitOne_star 0 0))

omit [Nontrivial E] in
theorem compatibleCornerUnit_mul :
    compatibleCornerUnit data left * compatibleCornerUnit data left =
      compatibleCornerUnit data left := by
  exact (map_mul left _ _).symm.trans
    (congrArg left (compatible_matrixUnitOne_mul 0 0 0))

omit [Nontrivial E] in
include compatible in
theorem compatible_common_apply (c : edgeSumAlgebra data) :
    left (amalgamLeftInclusion data c) =
      right (amalgamRightInclusion data c) := by
  exact congrArg (fun f : edgeSumAlgebra data →⋆ₐ[ℂ] E ↦ f c) compatible

omit [Nontrivial E] in
include compatible in
theorem compatibleCornerUnit_eq_right :
    compatibleCornerUnit data left = compatibleMatrixUnitRight data right 0 0 := by
  have h := compatible_common_apply data left right compatible
    ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data))
  have hL : amalgamLeftInclusion data
        ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data)) =
      cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data) := by
    change cStarDiagonalTwo (1 : baseAlgebra data) 0 = _
    exact cStarDiagonalTwo_one_zero
  have hR : amalgamRightInclusion data
        ((1 : sourceEdgeAlgebra data), (0 : targetEdgeAlgebra data)) =
      cStarMatrixUnitTwo 0 0 (1 : sourceEdgeAlgebra data) := by
    change cStarDiagonalTwo (1 : sourceEdgeAlgebra data)
      ((edgeIsomorphism data).symm (0 : targetEdgeAlgebra data)) = _
    rw [map_zero]
    exact cStarDiagonalTwo_one_zero
  exact (congrArg left hL.symm).trans (h.trans (congrArg right hR))

omit [Nontrivial E] in
include compatible in
theorem compatibleMatrixUnit_one_one_common :
    compatibleMatrixUnitLeft data left 1 1 =
      compatibleMatrixUnitRight data right 1 1 := by
  have h := compatible_common_apply data left right compatible
    ((0 : sourceEdgeAlgebra data), (1 : targetEdgeAlgebra data))
  have hL : amalgamLeftInclusion data
        ((0 : sourceEdgeAlgebra data), (1 : targetEdgeAlgebra data)) =
      cStarMatrixUnitTwo 1 1 (1 : baseAlgebra data) := by
    change cStarDiagonalTwo (0 : baseAlgebra data) 1 = _
    exact cStarDiagonalTwo_zero_one
  have hR : amalgamRightInclusion data
        ((0 : sourceEdgeAlgebra data), (1 : targetEdgeAlgebra data)) =
      cStarMatrixUnitTwo 1 1 (1 : sourceEdgeAlgebra data) := by
    change cStarDiagonalTwo (0 : sourceEdgeAlgebra data)
      ((edgeIsomorphism data).symm (1 : targetEdgeAlgebra data)) = _
    rw [map_one]
    exact cStarDiagonalTwo_zero_one
  exact (congrArg left hL.symm).trans (h.trans (congrArg right hR))

abbrev CompatibleCorner := CStarCorner (compatibleCornerUnit data left)
  (compatibleCornerUnit_star data left) (compatibleCornerUnit_mul data left)

/-- The corner unit is not zero.  In `M₂` it is one of two matrix units
summing to `1`, and `e₁₀ = e₁₀e₀₀`, `e₁₁ = e₁₀e₀₁`, so killing `e₀₀` would kill
`e₁₀`, then `e₁₁`, then `1` — impossible in a nontrivial `E` because `left` is
unital.  This is exactly what `CStarHNNRepresentation.ofCovariantPair` needs of
its carrier, and no `Nontrivial` instance for a C*-corner can hold without
it. -/
theorem compatibleCornerUnit_ne_zero :
    compatibleCornerUnit data left ≠ 0 := by
  intro h
  have h00 : left (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data)) = 0 := h
  have hmul10 :
      left (cStarMatrixUnitTwo 1 0 (1 : baseAlgebra data)) *
          left (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data)) =
        left (cStarMatrixUnitTwo 1 0 (1 : baseAlgebra data)) :=
    (map_mul left _ _).symm.trans
      (congrArg left (compatible_matrixUnitOne_mul 1 0 0))
  have h10 : left (cStarMatrixUnitTwo 1 0 (1 : baseAlgebra data)) = 0 := by
    rw [← hmul10, h00, mul_zero]
  have hmul11 :
      left (cStarMatrixUnitTwo 1 0 (1 : baseAlgebra data)) *
          left (cStarMatrixUnitTwo 0 1 (1 : baseAlgebra data)) =
        left (cStarMatrixUnitTwo 1 1 (1 : baseAlgebra data)) :=
    (map_mul left _ _).symm.trans
      (congrArg left (compatible_matrixUnitOne_mul 1 0 1))
  have h11 : left (cStarMatrixUnitTwo 1 1 (1 : baseAlgebra data)) = 0 := by
    rw [← hmul11, h10, zero_mul]
  have hsum :
      left (cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data)) +
          left (cStarMatrixUnitTwo 1 1 (1 : baseAlgebra data)) = 1 :=
    ((map_add left _ _).symm.trans
      (congrArg left compatible_matrixUnitOne_add)).trans (map_one left)
  rw [h00, h11, add_zero] at hsum
  exact one_ne_zero hsum.symm

/-- The Ueda corner of a compatible coordinate is nontrivial. -/
instance compatibleCornerNontrivial :
    Nontrivial (CompatibleCorner data left) := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro hone
  have hval := congrArg Subtype.val hone
  exact compatibleCornerUnit_ne_zero data left hval

omit [Nontrivial E] in
include compatible in
theorem exists_compatibleCornerWord_unitary :
    ∃ w : unitary (CompatibleCorner data left),
      ((w : CompatibleCorner data left) : E) =
        compatibleMatrixUnitLeft data left 0 1 *
          compatibleMatrixUnitRight data right 1 0 := by
  refine manuscriptSentence_6e8a0c1082a2_cornerWordUnitary
    (compatibleCornerUnit data left)
    (compatibleMatrixUnitLeft data left 0 1)
    (compatibleMatrixUnitLeft data left 1 0)
    (compatibleMatrixUnitLeft data left 1 1)
    (compatibleMatrixUnitRight data right 0 1)
    (compatibleMatrixUnitRight data right 1 0)
    (compatibleMatrixUnitRight data right 1 1)
    (compatibleCornerUnit_star data left) (compatibleCornerUnit_mul data left)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (compatibleMatrixUnit_one_one_common data left right compatible)
  · exact (map_star left _).symm.trans
      (congrArg left (compatible_matrixUnitOne_star 0 1))
  · exact (map_star right _).symm.trans
      (congrArg right (compatible_matrixUnitOne_star 1 0))
  · exact (map_mul left _ _).symm.trans
      (congrArg left (compatible_matrixUnitOne_mul 0 0 1))
  · rw [compatibleCornerUnit_eq_right data left right compatible]
    exact (map_mul right _ _).symm.trans
      (congrArg right (compatible_matrixUnitOne_mul 1 0 0))
  · exact (map_mul right _ _).symm.trans
      (congrArg right (compatible_matrixUnitOne_mul 1 0 1))
  · exact (map_mul left _ _).symm.trans
      (congrArg left (compatible_matrixUnitOne_mul 0 1 1))
  · exact (map_mul left _ _).symm.trans
      (congrArg left (compatible_matrixUnitOne_mul 0 1 0))
  · exact (map_mul left _ _).symm.trans
      (congrArg left (compatible_matrixUnitOne_mul 1 0 1))
  · exact (map_mul right _ _).symm.trans
      (congrArg right (compatible_matrixUnitOne_mul 0 1 1))
  · rw [compatibleCornerUnit_eq_right data left right compatible]
    exact (map_mul right _ _).symm.trans
      (congrArg right (compatible_matrixUnitOne_mul 0 1 0))

def compatibleCornerBaseElement (d : baseAlgebra data) :
    CompatibleCorner data left :=
  ⟨left (cStarDiagonalTwo d 0), by
    constructor
    · exact (map_mul left _ _).symm.trans (congrArg left (by
        calc
          cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data) *
              cStarDiagonalTwo d 0 = cStarMatrixUnitTwo 0 0 (1 * d) :=
            cStarMatrixUnitTwo_mul_diagonal 1 d 0 0 0
          _ = cStarMatrixUnitTwo 0 0 d := by rw [one_mul]
          _ = cStarDiagonalTwo d 0 :=
            (cStarDiagonalTwo_eq_matrixUnit_zero d).symm))
    · exact (map_mul left _ _).symm.trans (congrArg left (by
        calc
          cStarDiagonalTwo d 0 *
              cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data) =
              cStarMatrixUnitTwo 0 0 (d * 1) :=
            cStarDiagonalTwo_mul_unit d 0 1 0 0
          _ = cStarMatrixUnitTwo 0 0 d := by rw [mul_one]
          _ = cStarDiagonalTwo d 0 :=
            (cStarDiagonalTwo_eq_matrixUnit_zero d).symm))⟩

def compatibleCornerBaseMap : baseAlgebra data →⋆ₐ[ℂ]
    CompatibleCorner data left where
  toFun := compatibleCornerBaseElement data left
  map_one' := by
    apply Subtype.ext
    exact congrArg left cStarDiagonalTwo_one_zero
  map_mul' d e := by
    apply Subtype.ext
    exact (congrArg left (diagonalZero_mul_diagonalZero d e).symm).trans
      (map_mul left _ _)
  map_zero' := by
    apply Subtype.ext
    exact (congrArg left diagonalZero_zero).trans (map_zero left)
  map_add' d e := by
    apply Subtype.ext
    exact (congrArg left (diagonalZero_add_diagonalZero d e).symm).trans
      (map_add left _ _)
  commutes' r := by
    apply Subtype.ext
    exact (congrArg left (diagonalZero_algebraMap r)).trans
      (map_smul left r _)
  map_star' d := by
    apply Subtype.ext
    exact (congrArg left (star_diagonalZero d).symm).trans
      (map_star left _)

def compatibleCornerStableUnitary : unitary (CompatibleCorner data left) :=
  (exists_compatibleCornerWord_unitary data left right compatible).choose

omit [Nontrivial E] in
include compatible in
theorem compatible_diagonal_source_zero_common (b : sourceEdgeAlgebra data) :
    left (cStarDiagonalTwo (b : baseAlgebra data) 0) =
      right (cStarDiagonalTwo b 0) := by
  have h := compatible_common_apply data left right compatible
    (b, (0 : targetEdgeAlgebra data))
  change left (cStarDiagonalTwo (b : baseAlgebra data)
      ((0 : targetEdgeAlgebra data) : baseAlgebra data)) =
    right (cStarDiagonalTwo b
      ((edgeIsomorphism data).symm (0 : targetEdgeAlgebra data))) at h
  simpa only [ZeroMemClass.coe_zero, map_zero] using h

omit [Nontrivial E] in
include compatible in
theorem compatible_zero_diagonal_edge_common (b : sourceEdgeAlgebra data) :
    right (cStarDiagonalTwo 0 b) =
      left (cStarDiagonalTwo 0
        ((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) := by
  have h := compatible_common_apply data left right compatible
    ((0 : sourceEdgeAlgebra data), edgeIsomorphism data b)
  change left (cStarDiagonalTwo
      ((0 : sourceEdgeAlgebra data) : baseAlgebra data)
      ((edgeIsomorphism data b : targetEdgeAlgebra data) :
        baseAlgebra data)) =
    right (cStarDiagonalTwo (0 : sourceEdgeAlgebra data)
      ((edgeIsomorphism data).symm (edgeIsomorphism data b))) at h
  simpa only [ZeroMemClass.coe_zero, StarAlgEquiv.symm_apply_apply] using h.symm

omit [Nontrivial E] in
theorem compatible_right_source_sandwich (b : sourceEdgeAlgebra data) :
    compatibleMatrixUnitRight data right 1 0 *
        right (cStarDiagonalTwo b 0) *
      compatibleMatrixUnitRight data right 0 1 =
        right (cStarDiagonalTwo 0 b) := by
  change right (cStarMatrixUnitTwo 1 0 1) *
      right (cStarDiagonalTwo b 0) * right (cStarMatrixUnitTwo 0 1 1) = _
  rw [← map_mul right, ← map_mul right]
  exact congrArg right (matrixUnit_ten_diagonal_zero_zeroOne b)

omit [Nontrivial E] in
theorem compatible_left_target_sandwich (c : targetEdgeAlgebra data) :
    compatibleMatrixUnitLeft data left 0 1 *
        left (cStarDiagonalTwo 0 (c : baseAlgebra data)) *
      compatibleMatrixUnitLeft data left 1 0 =
        left (cStarDiagonalTwo (c : baseAlgebra data) 0) := by
  change left (cStarMatrixUnitTwo 0 1 1) *
      left (cStarDiagonalTwo 0 (c : baseAlgebra data)) *
      left (cStarMatrixUnitTwo 1 0 1) = _
  rw [← map_mul left, ← map_mul left]
  exact congrArg left (matrixUnit_zeroOne_zeroDiagonal_ten (c : baseAlgebra data))

omit [Nontrivial E] in
include compatible in
theorem compatibleCornerWord_covariance_ambient (b : sourceEdgeAlgebra data) :
    (compatibleMatrixUnitLeft data left 0 1 *
        compatibleMatrixUnitRight data right 1 0) *
        left (cStarDiagonalTwo (b : baseAlgebra data) 0) *
      star (compatibleMatrixUnitLeft data left 0 1 *
        compatibleMatrixUnitRight data right 1 0) =
      left (cStarDiagonalTwo
        ((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data) 0) := by
  have hstarL : star (compatibleMatrixUnitLeft data left 0 1) =
      compatibleMatrixUnitLeft data left 1 0 :=
    (map_star left _).symm.trans
      (congrArg left (compatible_matrixUnitOne_star 0 1))
  have hstarR : star (compatibleMatrixUnitRight data right 1 0) =
      compatibleMatrixUnitRight data right 0 1 :=
    (map_star right _).symm.trans
      (congrArg right (compatible_matrixUnitOne_star 1 0))
  rw [star_mul, hstarR, hstarL,
    compatible_diagonal_source_zero_common data left right compatible]
  calc
    _ = compatibleMatrixUnitLeft data left 0 1 *
        (compatibleMatrixUnitRight data right 1 0 *
          right (cStarDiagonalTwo b 0) *
          compatibleMatrixUnitRight data right 0 1) *
        compatibleMatrixUnitLeft data left 1 0 := by simp only [mul_assoc]
    _ = compatibleMatrixUnitLeft data left 0 1 *
        right (cStarDiagonalTwo 0 b) *
        compatibleMatrixUnitLeft data left 1 0 := by
      rw [compatible_right_source_sandwich data right]
    _ = compatibleMatrixUnitLeft data left 0 1 *
        left (cStarDiagonalTwo 0
          ((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data)) *
        compatibleMatrixUnitLeft data left 1 0 := by
      rw [compatible_zero_diagonal_edge_common data left right compatible]
    _ = _ := compatible_left_target_sandwich data left (edgeIsomorphism data b)

omit [Nontrivial E] in
theorem compatibleCornerStable_covariance_conj (b : sourceEdgeAlgebra data) :
    (compatibleCornerStableUnitary data left right compatible :
        CompatibleCorner data left) *
        compatibleCornerBaseMap data left (b : baseAlgebra data) *
      star (compatibleCornerStableUnitary data left right compatible :
        CompatibleCorner data left) =
      compatibleCornerBaseMap data left
        ((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data) := by
  apply Subtype.ext
  have hw : (((compatibleCornerStableUnitary data left right compatible :
          unitary (CompatibleCorner data left)) :
        CompatibleCorner data left) : E) =
      compatibleMatrixUnitLeft data left 0 1 *
        compatibleMatrixUnitRight data right 1 0 :=
    (exists_compatibleCornerWord_unitary data left right compatible).choose_spec
  have hambient :=
    compatibleCornerWord_covariance_ambient data left right compatible b
  rw [← hw] at hambient
  exact hambient

omit [Nontrivial E] in
theorem compatibleCornerStable_covariance (b : sourceEdgeAlgebra data) :
    (compatibleCornerStableUnitary data left right compatible :
        CompatibleCorner data left) *
        compatibleCornerBaseMap data left (b : baseAlgebra data) =
      compatibleCornerBaseMap data left
          ((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data) *
        (compatibleCornerStableUnitary data left right compatible :
          CompatibleCorner data left) := by
  calc
    _ = ((compatibleCornerStableUnitary data left right compatible :
          CompatibleCorner data left) *
        compatibleCornerBaseMap data left (b : baseAlgebra data) *
        star (compatibleCornerStableUnitary data left right compatible :
          CompatibleCorner data left)) *
        (compatibleCornerStableUnitary data left right compatible :
          CompatibleCorner data left) := by
      rw [mul_assoc,
        (compatibleCornerStableUnitary data left right compatible).property.1,
        mul_one]
    _ = _ := by rw [compatibleCornerStable_covariance_conj]

def compatibleCornerHNNRepresentation : CStarHNNRepresentation
    (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data) :=
  CStarHNNRepresentation.ofCovariantPair
    (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data)
    (compatibleCornerBaseMap data left)
    (compatibleCornerStableUnitary data left right compatible)
    (compatibleCornerStable_covariance data left right compatible)

/-- Closed no-input endpoint for the explicit compatible-coordinate corner. -/
def ExplicitCompatibleCoordinateCorner : Prop :=
  ∀ {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
    {A : Type} [CStarAlgebra A]
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (data : CoronaConjugator G S T phi A X)
    {E : Type} [CStarAlgebra E] [Nontrivial E]
    (left : matrixBaseAlgebra data →⋆ₐ[ℂ] E)
    (right : matrixEdgeAlgebra data →⋆ₐ[ℂ] E)
    (_compatible : left.comp (amalgamLeftInclusion data) =
      right.comp (amalgamRightInclusion data)),
      Nonempty (CStarHNNRepresentation
        (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
        (edgeIsomorphism data))

theorem explicitCompatibleCoordinateCorner :
    ExplicitCompatibleCoordinateCorner := by
  intro G _ S T phi A _ X _ data E _ _ left right compatible
  exact ⟨compatibleCornerHNNRepresentation data left right compatible⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.HNNPermanence.explicitCompatibleCoordinateCorner
