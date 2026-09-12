import GroupApproximation.Analysis.CStarCPConvex
import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Meta.AxiomGuard

/-!
# A binary matrix-block UCP retract

This file realizes a finite product of two full matrix algebras as the
block-diagonal range in one full matrix algebra.  The map back is not merely
the algebraic extraction of the two diagonal blocks: it is constructed as a
pair of row-Gram Choi maps, so complete positivity is proved internally.

The composite on the ambient full matrix algebra is therefore the unital
completely positive conditional expectation which deletes the two off-diagonal
blocks.  This is the binary induction step needed to turn a finite Wedderburn
product into a retract of one matrix algebra.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open GroupApproximation.CStarExactness
open scoped Matrix.Norms.L2Operator

universe u

noncomputable section

local instance matrixBlockCStarAlgebraForBlockRetract
    (Y : Type) [Fintype Y] [DecidableEq Y] [Nonempty Y] :
    CStarAlgebra (Matrix Y Y ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-! ## Choi maps indexed by an arbitrary finite type -/

/-- The row-Gram Choi map with an arbitrary nonempty finite indexing type. -/
def finiteMatrixRowChoiMap
    {Y : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {B : Type u} [CStarAlgebra B] (b : Y → B) :
    Matrix Y Y ℂ →ₗ[ℂ] B :=
  (matrixRowChoiMap (fun i ↦ b ((Fintype.equivFin Y).symm i))).comp
    ((matrixReindexStarAlgEquiv (Fintype.equivFin Y)).toStarAlgHom.toNonUnitalStarAlgHom :
      Matrix Y Y ℂ →ₗ[ℂ]
        Matrix (Fin (Fintype.card Y)) (Fin (Fintype.card Y)) ℂ)

/-- Arbitrarily indexed row-Gram Choi maps are completely positive. -/
theorem isCompletelyPositive_finiteMatrixRowChoiMap
    {Y : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {B : Type u} [CStarAlgebra B] (b : Y → B) :
    CStarExactness.IsCompletelyPositive (finiteMatrixRowChoiMap b) := by
  exact (isCompletelyPositive_matrixRowChoiMap
    (fun i ↦ b ((Fintype.equivFin Y).symm i))).comp
      (CStarExactness.isCompletelyPositive_of_starAlgHom
        (matrixReindexStarAlgEquiv (Fintype.equivFin Y)).toStarAlgHom.toNonUnitalStarAlgHom)

@[simp] theorem finiteMatrixRowChoiMap_apply
    {Y : Type} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {B : Type u} [CStarAlgebra B] (b : Y → B) (T : Matrix Y Y ℂ) :
    finiteMatrixRowChoiMap b T =
      ∑ i : Y, ∑ j : Y, T i j • (star (b i) * b j) := by
  rw [finiteMatrixRowChoiMap, LinearMap.comp_apply, matrixRowChoiMap_apply]
  symm
  refine Fintype.sum_equiv (Fintype.equivFin Y) _ _ fun i ↦ ?_
  refine Fintype.sum_equiv (Fintype.equivFin Y) _ _ fun j ↦ ?_
  simp [matrixReindexStarAlgEquiv]

/-! ## The two diagonal-block compressions -/

variable (Y Z : FiniteModel) [Nonempty Y] [Nonempty Z]

/-- The matrix-unit Gram identity, with an arbitrary finite index type. -/
theorem star_single_row_mul_single_row_finite
    {W : Type} [Fintype W] [DecidableEq W] (o i j : W) :
    star (Matrix.single o i (1 : ℂ)) * Matrix.single o j (1 : ℂ) =
      Matrix.single i j 1 := by
  have hstar : star (Matrix.single o i (1 : ℂ)) =
      Matrix.single i o (1 : ℂ) := by
    funext p q
    show star ((Matrix.single o i (1 : ℂ)) q p) =
      (Matrix.single i o (1 : ℂ)) p q
    rw [Matrix.single_apply, Matrix.single_apply]
    by_cases h₁ : o = q <;> by_cases h₂ : i = p <;>
      simp [h₁, h₂, and_comm]
  rw [hstar, Matrix.single_mul_single_same, one_mul]

/-- Matrix-unit expansion with an arbitrary finite index type. -/
theorem matrix_eq_sum_smul_single_finite
    {W : Type} [Fintype W] [DecidableEq W] (T : Matrix W W ℂ) :
    T = ∑ i : W, ∑ j : W, T i j • Matrix.single i j 1 := by
  classical
  ext p q
  rw [Matrix.sum_apply, Finset.sum_eq_single p]
  · rw [Matrix.sum_apply, Finset.sum_eq_single q]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  · intro i _ hi
    simp [Matrix.sum_apply, hi]
  · simp

/-- A matrix-unit row selecting the left summand of `Y ⊕ Z`. -/
def leftBlockChoiTuple : Y ⊕ Z → Matrix Y Y ℂ
  | Sum.inl y => Matrix.single (Classical.choice inferInstance) y 1
  | Sum.inr _ => 0

/-- The UCP compression of a matrix on `Y ⊕ Z` to its left diagonal block. -/
def leftBlockCompression :
    Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ →ₗ[ℂ] Matrix Y Y ℂ :=
  finiteMatrixRowChoiMap (leftBlockChoiTuple Y Z)

theorem isCompletelyPositive_leftBlockCompression :
    CStarExactness.IsCompletelyPositive (leftBlockCompression Y Z) :=
  isCompletelyPositive_finiteMatrixRowChoiMap _

/-- A matrix-unit row selecting the right summand of `Y ⊕ Z`. -/
def rightBlockChoiTuple : Y ⊕ Z → Matrix Z Z ℂ
  | Sum.inl _ => 0
  | Sum.inr z => Matrix.single (Classical.choice inferInstance) z 1

/-- The UCP compression of a matrix on `Y ⊕ Z` to its right diagonal block. -/
def rightBlockCompression :
    Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ →ₗ[ℂ] Matrix Z Z ℂ :=
  finiteMatrixRowChoiMap (rightBlockChoiTuple Y Z)

omit [Nonempty Y] in
theorem isCompletelyPositive_rightBlockCompression :
    CStarExactness.IsCompletelyPositive (rightBlockCompression Y Z) :=
  isCompletelyPositive_finiteMatrixRowChoiMap _

@[simp] theorem leftBlockCompression_blockDiag
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    leftBlockCompression Y Z (blockDiagMatrix Y Z A B) = A := by
  classical
  rw [leftBlockCompression, finiteMatrixRowChoiMap_apply]
  simp only [Fintype.sum_sum_type, leftBlockChoiTuple,
    blockDiagMatrix, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, star_zero,
    zero_mul, mul_zero, smul_zero, Finset.sum_const_zero, add_zero,
    star_single_row_mul_single_row_finite]
  exact (matrix_eq_sum_smul_single_finite A).symm

omit [Nonempty Y] in
@[simp] theorem rightBlockCompression_blockDiag
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    rightBlockCompression Y Z (blockDiagMatrix Y Z A B) = B := by
  classical
  rw [rightBlockCompression, finiteMatrixRowChoiMap_apply]
  simp only [Fintype.sum_sum_type, rightBlockChoiTuple,
    blockDiagMatrix,
    Matrix.fromBlocks_apply₂₂, star_zero,
    zero_mul, mul_zero, smul_zero, Finset.sum_const_zero,
    zero_add, star_single_row_mul_single_row_finite]
  exact (matrix_eq_sum_smul_single_finite B).symm

/-! ## The binary retract and its conditional expectation -/

/-- Block-diagonal inclusion of a binary product into one full matrix algebra. -/
def binaryBlockDiagStarAlgHom :
    (Matrix Y Y ℂ × Matrix Z Z ℂ) →⋆ₐ[ℂ]
      Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ where
  toFun x := blockDiagMatrix Y Z x.1 x.2
  map_zero' := MFAlgebraDimension.blockDiagMatrix_zero Y Z
  map_one' := blockDiagMatrix_one Y Z
  map_add' x y :=
    (MFAlgebraDimension.blockDiagMatrix_add Y Z x.1 y.1 x.2 y.2).symm
  map_mul' x y := (blockDiagMatrix_mul Y Z x.1 y.1 x.2 y.2).symm
  commutes' c := by
    ext p q
    cases p <;> cases q <;>
      simp [blockDiagMatrix, Matrix.fromBlocks,
        Matrix.algebraMap_matrix_apply]
  map_star' x := by
    change blockDiagMatrix Y Z (star x.1) (star x.2) =
      star (blockDiagMatrix Y Z x.1 x.2)
    simpa [Matrix.star_eq_conjTranspose] using
      (blockDiagMatrix_conjTranspose Y Z x.1 x.2).symm

/-- The pair of diagonal-block compressions. -/
def binaryBlockRetraction :
    Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ →ₗ[ℂ]
      (Matrix Y Y ℂ × Matrix Z Z ℂ) where
  toFun T := (leftBlockCompression Y Z T, rightBlockCompression Y Z T)
  map_add' S T := by simp
  map_smul' c T := by simp

/-- The binary block retraction is completely positive. -/
theorem isCompletelyPositive_binaryBlockRetraction :
    CStarExactness.IsCompletelyPositive (binaryBlockRetraction Y Z) := by
  intro n M hM
  obtain ⟨P, hP⟩ := isCompletelyPositive_leftBlockCompression Y Z n M hM
  obtain ⟨Q, hQ⟩ := isCompletelyPositive_rightBlockCompression Y Z n M hM
  let R : CStarMatrix (Fin n) (Fin n)
      (Matrix Y Y ℂ × Matrix Z Z ℂ) := fun i j ↦ (P i j, Q i j)
  refine ⟨R, ?_⟩
  funext i j
  apply Prod.ext
  · calc
      ((M.map ⇑(binaryBlockRetraction Y Z)) i j).1 =
          (M.map ⇑(leftBlockCompression Y Z)) i j := rfl
      _ = (star P * P) i j := congrFun (congrFun hP i) j
      _ = ((star R * R) i j).1 := by
        let fstAH : (Matrix Y Y ℂ × Matrix Z Z ℂ) →+ Matrix Y Y ℂ :=
          { toFun := Prod.fst
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        rw [cstarMatrix_mul_apply, cstarMatrix_mul_apply]
        simp only [cstarMatrix_star_apply]
        change (∑ x, star (P x i) * P x j) =
          fstAH (∑ x, star (R x i) * R x j)
        rw [map_sum]
        rfl
  · calc
      ((M.map ⇑(binaryBlockRetraction Y Z)) i j).2 =
          (M.map ⇑(rightBlockCompression Y Z)) i j := rfl
      _ = (star Q * Q) i j := congrFun (congrFun hQ i) j
      _ = ((star R * R) i j).2 := by
        let sndAH : (Matrix Y Y ℂ × Matrix Z Z ℂ) →+ Matrix Z Z ℂ :=
          { toFun := Prod.snd
            map_zero' := rfl
            map_add' := fun _ _ ↦ rfl }
        rw [cstarMatrix_mul_apply, cstarMatrix_mul_apply]
        simp only [cstarMatrix_star_apply]
        change (∑ x, star (Q x i) * Q x j) =
          sndAH (∑ x, star (R x i) * R x j)
        rw [map_sum]
        rfl

@[simp] theorem binaryBlockRetraction_blockDiag (x :
    Matrix Y Y ℂ × Matrix Z Z ℂ) :
    binaryBlockRetraction Y Z (binaryBlockDiagStarAlgHom Y Z x) = x := by
  apply Prod.ext
  · exact leftBlockCompression_blockDiag Y Z x.1 x.2
  · exact rightBlockCompression_blockDiag Y Z x.1 x.2

theorem binaryBlockRetraction_one :
    binaryBlockRetraction Y Z 1 = 1 := by
  rw [← map_one (binaryBlockDiagStarAlgHom Y Z),
    binaryBlockRetraction_blockDiag]

/-- The UCP conditional expectation onto the binary block-diagonal range. -/
def binaryBlockConditionalExpectation :
    Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ →ₗ[ℂ]
      Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ :=
  (binaryBlockDiagStarAlgHom Y Z :
    (Matrix Y Y ℂ × Matrix Z Z ℂ) →ₗ[ℂ]
      Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ).comp
        (binaryBlockRetraction Y Z)

theorem isCompletelyPositive_binaryBlockConditionalExpectation :
    CStarExactness.IsCompletelyPositive
      (binaryBlockConditionalExpectation Y Z) :=
  (CStarExactness.isCompletelyPositive_of_starAlgHom
    (binaryBlockDiagStarAlgHom Y Z).toNonUnitalStarAlgHom).comp
      (isCompletelyPositive_binaryBlockRetraction Y Z)

theorem binaryBlockConditionalExpectation_one :
    binaryBlockConditionalExpectation Y Z 1 = 1 := by
  change binaryBlockDiagStarAlgHom Y Z (binaryBlockRetraction Y Z 1) = 1
  rw [binaryBlockRetraction_one, map_one]

@[simp] theorem binaryBlockConditionalExpectation_blockDiag
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    binaryBlockConditionalExpectation Y Z (blockDiagMatrix Y Z A B) =
      blockDiagMatrix Y Z A B := by
  change binaryBlockDiagStarAlgHom Y Z
      (binaryBlockRetraction Y Z (blockDiagMatrix Y Z A B)) =
    blockDiagMatrix Y Z A B
  rw [show blockDiagMatrix Y Z A B =
      binaryBlockDiagStarAlgHom Y Z (A, B) from rfl,
    binaryBlockRetraction_blockDiag]

theorem binaryBlockConditionalExpectation_idempotent (T :
    Matrix (Y ⊕ Z) (Y ⊕ Z) ℂ) :
    binaryBlockConditionalExpectation Y Z
      (binaryBlockConditionalExpectation Y Z T) =
        binaryBlockConditionalExpectation Y Z T := by
  change binaryBlockDiagStarAlgHom Y Z
      (binaryBlockRetraction Y Z
        (binaryBlockDiagStarAlgHom Y Z (binaryBlockRetraction Y Z T))) =
    binaryBlockDiagStarAlgHom Y Z (binaryBlockRetraction Y Z T)
  rw [binaryBlockRetraction_blockDiag]

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms isCompletelyPositive_finiteMatrixRowChoiMap
#audit_axioms isCompletelyPositive_binaryBlockRetraction
#audit_axioms binaryBlockRetraction_blockDiag
#audit_axioms isCompletelyPositive_binaryBlockConditionalExpectation
#audit_axioms binaryBlockConditionalExpectation_idempotent
