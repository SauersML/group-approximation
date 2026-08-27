import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaAmalgamPackage
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaMatrixIdentities
import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUniversalDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Ueda corners in compatible representation coordinates

Every same-universe compatible representation of the two matrix factors
contains the Ueda corner.  The corner carries a covariant representation of
the HNN datum.  This coordinate construction avoids the universe increase of
the two concrete universal products.
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

abbrev CoordinateAmalgamRepresentation := CStarAmalgamRepresentation
  (amalgamLeftInclusion data) (amalgamRightInclusion data)

variable (Q : CoordinateAmalgamRepresentation data)

def coordinateMatrixUnitLeft (i j : Fin 2) : Q.carrier :=
  Q.left (cStarMatrixUnitTwo i j (1 : baseAlgebra data))

def coordinateMatrixUnitRight (i j : Fin 2) : Q.carrier :=
  Q.right (cStarMatrixUnitTwo i j (1 : sourceEdgeAlgebra data))

def coordinateCornerUnit : Q.carrier := coordinateMatrixUnitLeft data Q 0 0

theorem coordinate_matrixUnitOne_star {K : Type} [CStarAlgebra K]
    (i j : Fin 2) :
    star (cStarMatrixUnitTwo i j (1 : K)) =
      cStarMatrixUnitTwo j i (1 : K) := by
  rw [star_cStarMatrixUnitTwo, star_one]

theorem coordinate_matrixUnitOne_mul {K : Type} [CStarAlgebra K]
    (i j l : Fin 2) :
    cStarMatrixUnitTwo i j (1 : K) * cStarMatrixUnitTwo j l (1 : K) =
      cStarMatrixUnitTwo i l (1 : K) := by
  rw [cStarMatrixUnitTwo_mul]
  simp

theorem coordinateCornerUnit_star :
    star (coordinateCornerUnit data Q) = coordinateCornerUnit data Q := by
  exact (Q.left.map_star _).symm.trans
    (congrArg Q.left (coordinate_matrixUnitOne_star 0 0))

theorem coordinateCornerUnit_mul :
    coordinateCornerUnit data Q * coordinateCornerUnit data Q =
      coordinateCornerUnit data Q := by
  exact (Q.left.map_mul _ _).symm.trans
    (congrArg Q.left (coordinate_matrixUnitOne_mul 0 0 0))

theorem coordinate_common_apply (c : edgeSumAlgebra data) :
    Q.left (amalgamLeftInclusion data c) =
      Q.right (amalgamRightInclusion data c) := by
  exact congrArg (fun f : edgeSumAlgebra data →⋆ₐ[ℂ] Q.carrier ↦ f c)
    Q.compatible

theorem coordinateCornerUnit_eq_right :
    coordinateCornerUnit data Q = coordinateMatrixUnitRight data Q 0 0 := by
  have h := coordinate_common_apply data Q
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
  exact (congrArg Q.left hL.symm).trans (h.trans (congrArg Q.right hR))

theorem coordinateMatrixUnit_one_one_common :
    coordinateMatrixUnitLeft data Q 1 1 =
      coordinateMatrixUnitRight data Q 1 1 := by
  have h := coordinate_common_apply data Q
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
  exact (congrArg Q.left hL.symm).trans (h.trans (congrArg Q.right hR))

theorem exists_coordinateCornerWord_unitary :
    ∃ w : unitary (CStarCorner (coordinateCornerUnit data Q)
        (coordinateCornerUnit_star data Q) (coordinateCornerUnit_mul data Q)),
      ((w : CStarCorner (coordinateCornerUnit data Q)
          (coordinateCornerUnit_star data Q)
          (coordinateCornerUnit_mul data Q)) : Q.carrier) =
        coordinateMatrixUnitLeft data Q 0 1 *
          coordinateMatrixUnitRight data Q 1 0 := by
  refine manuscriptSentence_6e8a0c1082a2_cornerWordUnitary
    (coordinateCornerUnit data Q)
    (coordinateMatrixUnitLeft data Q 0 1)
    (coordinateMatrixUnitLeft data Q 1 0)
    (coordinateMatrixUnitLeft data Q 1 1)
    (coordinateMatrixUnitRight data Q 0 1)
    (coordinateMatrixUnitRight data Q 1 0)
    (coordinateMatrixUnitRight data Q 1 1)
    (coordinateCornerUnit_star data Q) (coordinateCornerUnit_mul data Q)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (coordinateMatrixUnit_one_one_common data Q)
  · exact (Q.left.map_star _).symm.trans
      (congrArg Q.left (coordinate_matrixUnitOne_star 0 1))
  · exact (Q.right.map_star _).symm.trans
      (congrArg Q.right (coordinate_matrixUnitOne_star 1 0))
  · exact (Q.left.map_mul _ _).symm.trans
      (congrArg Q.left (coordinate_matrixUnitOne_mul 0 0 1))
  · rw [coordinateCornerUnit_eq_right]
    exact (Q.right.map_mul _ _).symm.trans
      (congrArg Q.right (coordinate_matrixUnitOne_mul 1 0 0))
  · exact (Q.right.map_mul _ _).symm.trans
      (congrArg Q.right (coordinate_matrixUnitOne_mul 1 0 1))
  · exact (Q.left.map_mul _ _).symm.trans
      (congrArg Q.left (coordinate_matrixUnitOne_mul 0 1 1))
  · exact (Q.left.map_mul _ _).symm.trans
      (congrArg Q.left (coordinate_matrixUnitOne_mul 0 1 0))
  · exact (Q.left.map_mul _ _).symm.trans
      (congrArg Q.left (coordinate_matrixUnitOne_mul 1 0 1))
  · exact (Q.right.map_mul _ _).symm.trans
      (congrArg Q.right (coordinate_matrixUnitOne_mul 0 1 1))
  · rw [coordinateCornerUnit_eq_right]
    exact (Q.right.map_mul _ _).symm.trans
      (congrArg Q.right (coordinate_matrixUnitOne_mul 0 1 0))

def coordinateCornerBaseElement (d : baseAlgebra data) :
    CStarCorner (coordinateCornerUnit data Q)
      (coordinateCornerUnit_star data Q) (coordinateCornerUnit_mul data Q) :=
  ⟨Q.left (cStarDiagonalTwo d 0), by
    constructor
    · have hm : cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data) *
          cStarDiagonalTwo d 0 = cStarDiagonalTwo d 0 := by
        calc
          _ = cStarMatrixUnitTwo 0 0 (1 * d) :=
            cStarMatrixUnitTwo_mul_diagonal 1 d 0 0 0
          _ = cStarMatrixUnitTwo 0 0 d := by rw [one_mul]
          _ = _ := (cStarDiagonalTwo_eq_matrixUnit_zero d).symm
      exact (Q.left.map_mul _ _).symm.trans (congrArg Q.left hm)
    · have hm : cStarDiagonalTwo d 0 *
          cStarMatrixUnitTwo 0 0 (1 : baseAlgebra data) =
          cStarDiagonalTwo d 0 := by
        calc
          _ = cStarMatrixUnitTwo 0 0 (d * 1) :=
            cStarDiagonalTwo_mul_unit d 0 1 0 0
          _ = cStarMatrixUnitTwo 0 0 d := by rw [mul_one]
          _ = _ := (cStarDiagonalTwo_eq_matrixUnit_zero d).symm
      exact (Q.left.map_mul _ _).symm.trans (congrArg Q.left hm)⟩

def coordinateCornerBaseMap :
    baseAlgebra data →⋆ₐ[ℂ]
      CStarCorner (coordinateCornerUnit data Q)
        (coordinateCornerUnit_star data Q) (coordinateCornerUnit_mul data Q) where
  toFun := coordinateCornerBaseElement data Q
  map_one' := by
    apply Subtype.ext
    exact congrArg Q.left cStarDiagonalTwo_one_zero
  map_mul' d e := by
    apply Subtype.ext
    change Q.left (cStarDiagonalTwo (d * e) 0) =
      Q.left (cStarDiagonalTwo d 0) * Q.left (cStarDiagonalTwo e 0)
    rw [← Q.left.map_mul]
    exact congrArg Q.left (by
      calc
        cStarDiagonalTwo (d * e) 0 = cStarDiagonalTwo (d * e) (0 * 0) := by
          rw [zero_mul]
        _ = cStarDiagonalTwo d 0 * cStarDiagonalTwo e 0 :=
          (cStarDiagonalTwo_mul d 0 e 0).symm)
  map_zero' := by
    apply Subtype.ext
    change Q.left (cStarDiagonalTwo 0 0) = 0
    rw [show cStarDiagonalTwo (0 : baseAlgebra data) 0 = 0 by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [cStarDiagonalTwo] <;> rfl,
      Q.left.map_zero]
  map_add' d e := by
    apply Subtype.ext
    change Q.left (cStarDiagonalTwo (d + e) 0) =
      Q.left (cStarDiagonalTwo d 0) + Q.left (cStarDiagonalTwo e 0)
    rw [← Q.left.map_add]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cStarDiagonalTwo] <;> rfl
  commutes' r := by
    apply Subtype.ext
    change Q.left (cStarDiagonalTwo (algebraMap ℂ _ r) 0) =
      r • coordinateCornerUnit data Q
    change Q.left (cStarDiagonalTwo (algebraMap ℂ _ r) 0) =
      r • Q.left (cStarMatrixUnitTwo 0 0 1)
    rw [← Q.left.map_smul]
    congr 1
    rw [Algebra.algebraMap_eq_smul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cStarDiagonalTwo, cStarMatrixUnitTwo]
  map_star' d := by
    apply Subtype.ext
    change Q.left (cStarDiagonalTwo (star d) 0) =
      star (Q.left (cStarDiagonalTwo d 0))
    exact (congrArg Q.left (star_cStarDiagonalTwo d 0).symm).trans
      (Q.left.map_star (cStarDiagonalTwo d 0))

def coordinateCornerStableUnitary :
    unitary (CStarCorner (coordinateCornerUnit data Q)
      (coordinateCornerUnit_star data Q) (coordinateCornerUnit_mul data Q)) :=
  (exists_coordinateCornerWord_unitary data Q).choose

theorem coordinate_diagonal_source_zero_common (b : sourceEdgeAlgebra data) :
    Q.left (cStarDiagonalTwo (b : baseAlgebra data) 0) =
      Q.right (cStarDiagonalTwo b 0) := by
  have h := coordinate_common_apply data Q
    (b, (0 : targetEdgeAlgebra data))
  change Q.left
      (cStarDiagonalTwo (b : baseAlgebra data)
        ((0 : targetEdgeAlgebra data) : baseAlgebra data)) =
    Q.right (cStarDiagonalTwo b
      ((edgeIsomorphism data).symm (0 : targetEdgeAlgebra data))) at h
  simpa only [ZeroMemClass.coe_zero, map_zero] using h

theorem coordinate_zero_diagonal_edge_common (b : sourceEdgeAlgebra data) :
    Q.right (cStarDiagonalTwo 0 b) =
      Q.left (cStarDiagonalTwo 0
        ((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data)) := by
  have h := coordinate_common_apply data Q
    ((0 : sourceEdgeAlgebra data), edgeIsomorphism data b)
  change Q.left (cStarDiagonalTwo
      ((0 : sourceEdgeAlgebra data) : baseAlgebra data)
      ((edgeIsomorphism data b : targetEdgeAlgebra data) :
        baseAlgebra data)) =
    Q.right (cStarDiagonalTwo (0 : sourceEdgeAlgebra data)
      ((edgeIsomorphism data).symm (edgeIsomorphism data b))) at h
  simpa only [ZeroMemClass.coe_zero, StarAlgEquiv.symm_apply_apply] using h.symm

theorem coordinate_right_source_sandwich (b : sourceEdgeAlgebra data) :
    coordinateMatrixUnitRight data Q 1 0 *
        Q.right (cStarDiagonalTwo b 0) *
      coordinateMatrixUnitRight data Q 0 1 =
        Q.right (cStarDiagonalTwo 0 b) := by
  change Q.right (cStarMatrixUnitTwo 1 0 1) *
      Q.right (cStarDiagonalTwo b 0) * Q.right (cStarMatrixUnitTwo 0 1 1) = _
  rw [← Q.right.map_mul, ← Q.right.map_mul]
  exact congrArg Q.right (matrixUnit_ten_diagonal_zero_zeroOne b)

theorem coordinate_left_target_sandwich (c : targetEdgeAlgebra data) :
    coordinateMatrixUnitLeft data Q 0 1 *
        Q.left (cStarDiagonalTwo 0 (c : baseAlgebra data)) *
      coordinateMatrixUnitLeft data Q 1 0 =
        Q.left (cStarDiagonalTwo (c : baseAlgebra data) 0) := by
  change Q.left (cStarMatrixUnitTwo 0 1 1) *
      Q.left (cStarDiagonalTwo 0 (c : baseAlgebra data)) *
        Q.left (cStarMatrixUnitTwo 1 0 1) = _
  rw [← Q.left.map_mul, ← Q.left.map_mul]
  exact congrArg Q.left (matrixUnit_zeroOne_zeroDiagonal_ten (c : baseAlgebra data))

theorem coordinateCornerWord_covariance_ambient (b : sourceEdgeAlgebra data) :
    (coordinateMatrixUnitLeft data Q 0 1 *
        coordinateMatrixUnitRight data Q 1 0) *
        Q.left (cStarDiagonalTwo (b : baseAlgebra data) 0) *
      star (coordinateMatrixUnitLeft data Q 0 1 *
        coordinateMatrixUnitRight data Q 1 0) =
      Q.left (cStarDiagonalTwo
        ((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data) 0) := by
  have hstarL : star (coordinateMatrixUnitLeft data Q 0 1) =
      coordinateMatrixUnitLeft data Q 1 0 :=
    (Q.left.map_star _).symm.trans
      (congrArg Q.left (coordinate_matrixUnitOne_star 0 1))
  have hstarR : star (coordinateMatrixUnitRight data Q 1 0) =
      coordinateMatrixUnitRight data Q 0 1 :=
    (Q.right.map_star _).symm.trans
      (congrArg Q.right (coordinate_matrixUnitOne_star 1 0))
  rw [star_mul, hstarR, hstarL, coordinate_diagonal_source_zero_common]
  calc
    _ = coordinateMatrixUnitLeft data Q 0 1 *
        (coordinateMatrixUnitRight data Q 1 0 *
          Q.right (cStarDiagonalTwo b 0) *
          coordinateMatrixUnitRight data Q 0 1) *
        coordinateMatrixUnitLeft data Q 1 0 := by simp only [mul_assoc]
    _ = coordinateMatrixUnitLeft data Q 0 1 *
        Q.right (cStarDiagonalTwo 0 b) *
        coordinateMatrixUnitLeft data Q 1 0 := by
      rw [coordinate_right_source_sandwich]
    _ = coordinateMatrixUnitLeft data Q 0 1 *
        Q.left (cStarDiagonalTwo 0
          ((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data)) *
        coordinateMatrixUnitLeft data Q 1 0 := by
      rw [coordinate_zero_diagonal_edge_common]
    _ = _ := coordinate_left_target_sandwich data Q (edgeIsomorphism data b)

theorem coordinateCornerStable_covariance_conj (b : sourceEdgeAlgebra data) :
    (coordinateCornerStableUnitary data Q :
        CStarCorner (coordinateCornerUnit data Q)
          (coordinateCornerUnit_star data Q) (coordinateCornerUnit_mul data Q)) *
        coordinateCornerBaseMap data Q (b : baseAlgebra data) *
      star (coordinateCornerStableUnitary data Q :
        CStarCorner (coordinateCornerUnit data Q)
          (coordinateCornerUnit_star data Q) (coordinateCornerUnit_mul data Q)) =
      coordinateCornerBaseMap data Q
        ((edgeIsomorphism data b : targetEdgeAlgebra data) :
          baseAlgebra data) := by
  apply Subtype.ext
  simpa only [(exists_coordinateCornerWord_unitary data Q).choose_spec] using
    coordinateCornerWord_covariance_ambient data Q b

theorem coordinateCornerStable_covariance (b : sourceEdgeAlgebra data) :
    (coordinateCornerStableUnitary data Q :
        CStarCorner (coordinateCornerUnit data Q)
          (coordinateCornerUnit_star data Q) (coordinateCornerUnit_mul data Q)) *
        coordinateCornerBaseMap data Q (b : baseAlgebra data) =
      coordinateCornerBaseMap data Q
          ((edgeIsomorphism data b : targetEdgeAlgebra data) :
            baseAlgebra data) *
        (coordinateCornerStableUnitary data Q :
          CStarCorner (coordinateCornerUnit data Q)
            (coordinateCornerUnit_star data Q)
            (coordinateCornerUnit_mul data Q)) := by
  calc
    _ = ((coordinateCornerStableUnitary data Q :
          CStarCorner (coordinateCornerUnit data Q)
            (coordinateCornerUnit_star data Q)
            (coordinateCornerUnit_mul data Q)) *
        coordinateCornerBaseMap data Q (b : baseAlgebra data) *
        star (coordinateCornerStableUnitary data Q :
          CStarCorner (coordinateCornerUnit data Q)
            (coordinateCornerUnit_star data Q)
            (coordinateCornerUnit_mul data Q))) *
        (coordinateCornerStableUnitary data Q :
          CStarCorner (coordinateCornerUnit data Q)
            (coordinateCornerUnit_star data Q)
            (coordinateCornerUnit_mul data Q)) := by
      rw [mul_assoc, (coordinateCornerStableUnitary data Q).property.1, mul_one]
    _ = _ := by rw [coordinateCornerStable_covariance_conj]

def coordinateHNNRepresentation : CStarHNNRepresentation
    (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data) :=
  CStarHNNRepresentation.ofCovariantPair
    (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data)
    (coordinateCornerBaseMap data Q) (coordinateCornerStableUnitary data Q)
    (coordinateCornerStable_covariance data Q)

/-- Closed endpoint: every compatible amalgam coordinate contains the
same-universe Ueda HNN corner. -/
def CompatibleCoordinateCarriesHNNCorner : Prop :=
  ∀ {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
    {A : Type} [CStarAlgebra A]
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (data : CoronaConjugator G S T phi A X)
    (Q : CoordinateAmalgamRepresentation data),
      Nonempty (CStarHNNRepresentation
        (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data))

theorem compatibleCoordinateCarriesHNNCorner :
    CompatibleCoordinateCarriesHNNCorner := by
  intro G _ S T phi A _ X _ data Q
  exact ⟨coordinateHNNRepresentation data Q⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.MFRecognition.HNNPermanence.compatibleCoordinateCarriesHNNCorner
