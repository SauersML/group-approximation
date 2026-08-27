import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Analysis.RationalNoncommutativeStarPolynomial

/-!
# Rational star polynomials in block-diagonal matrices

Evaluation commutes with binary block-diagonal assembly, and consequently the
operator norm of an evaluated block diagonal is the maximum of the two block
norms.  Iterating this lemma is the finite direct-sum step in the
reduced-product MF diagonal argument.
-/

namespace GroupApproximation
namespace RationalStarPolynomialBlockDiagonal

open RationalNoncommutativeStarPolynomial

open scoped Matrix.Norms.L2Operator

@[reducible] private noncomputable def
    matrixBlockCStarAlgebraForPolynomialBlockDiagonal
    (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W] :
    CStarAlgebra (Matrix W W ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

variable (Y Z : FiniteModel) [Nonempty Y] [Nonempty Z]

noncomputable local instance : CStarAlgebra (Matrix Y Y ℂ) :=
  matrixBlockCStarAlgebraForPolynomialBlockDiagonal Y

noncomputable local instance : CStarAlgebra (Matrix Z Z ℂ) :=
  matrixBlockCStarAlgebraForPolynomialBlockDiagonal Z

noncomputable local instance : CStarAlgebra
    (Matrix (blockSumModel Y Z) (blockSumModel Y Z) ℂ) :=
  matrixBlockCStarAlgebraForPolynomialBlockDiagonal (blockSumModel Y Z)

theorem eval_blockDiag (left : ℕ → Matrix Y Y ℂ)
    (right : ℕ → Matrix Z Z ℂ) (p : Polynomial) :
    eval (fun j ↦ blockDiagMatrix Y Z (left j) (right j)) p =
      blockDiagMatrix Y Z (eval left p) (eval right p) := by
  induction p with
  | zero =>
      rw [eval_zero, eval_zero, eval_zero]
      exact (MFAlgebraDimension.blockDiagMatrix_zero Y Z).symm
  | generator j => rfl
  | smul q p hp =>
      rw [eval_smul, hp, eval_smul, eval_smul]
      exact MFAlgebraDimension.blockDiagMatrix_smul Y Z _ _ _
  | add p q hp hq =>
      rw [eval_add, hp, hq, eval_add, eval_add]
      exact MFAlgebraDimension.blockDiagMatrix_add Y Z _ _ _ _
  | mul p q hp hq =>
      rw [eval_mul, hp, hq, eval_mul, eval_mul]
      exact blockDiagMatrix_mul Y Z _ _ _ _
  | star p hp =>
      rw [eval_star, hp, eval_star, eval_star, Matrix.star_eq_conjTranspose]
      exact blockDiagMatrix_conjTranspose Y Z _ _

theorem norm_eval_blockDiag (left : ℕ → Matrix Y Y ℂ)
    (right : ℕ → Matrix Z Z ℂ) (p : Polynomial) :
    ‖eval (fun j ↦ blockDiagMatrix Y Z (left j) (right j)) p‖ =
      max ‖eval left p‖ ‖eval right p‖ := by
  rw [eval_blockDiag, l2_opNorm_blockDiag]

end RationalStarPolynomialBlockDiagonal
end GroupApproximation
