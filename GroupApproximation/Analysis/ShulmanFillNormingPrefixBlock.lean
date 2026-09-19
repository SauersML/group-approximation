import GroupApproximation.Analysis.MFAlgebraDimensionNormalization
import GroupApproximation.Sofic.NormMFUniversalCorona

/-!
# Prefix block sums of a sequence of finite models

`Sofic/NormMFUniversalCorona` has the binary block diagonal `blockDiagMatrix`
with its product, unit, adjoint, difference and norm laws.  Iterating it along
an increasing prefix turns a *sequence* of matrices, one over each model, into
a single matrix over the block sum of the first `j + 1` models.

That is the construction behind "a bounded product of matrix algebras embeds in
a norm-matrix corona": send `(xₙ)ₙ` to the class of `j ↦ diag(x₀, …, x_j)`.
Because the entries are honest matrices — not corona classes — no
representative has to be chosen, and the map is a `*`-homomorphism on the nose.

This module builds `prefixModel` and `prefixDiag` and proves the algebra;
`Analysis/ShulmanFillNormingProductMF` does the norms and the embedding.

Only one `blockDiagMatrix` law is missing upstream, the `star` form of the
adjoint law; it is proved here from `blockDiagMatrix_conjTranspose`.
-/

namespace GroupApproximation
namespace ShulmanFill

open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## The one missing binary law

`MFAlgebraDimension` already supplies `blockDiagMatrix_zero`,
`blockDiagMatrix_add` and `blockDiagMatrix_smul`, and
`Sofic/NormMFUniversalCorona` the product, unit, difference and adjoint laws.
Only the `star` form of the adjoint law is absent. -/

theorem blockDiagMatrix_star (Y Z : FiniteModel)
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    star (blockDiagMatrix Y Z A B) =
      blockDiagMatrix Y Z (star A) (star B) := by
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.star_eq_conjTranspose, blockDiagMatrix_conjTranspose]

/-! ## The prefix models -/

/-- The block sum of the first `j + 1` models of a sequence. -/
def prefixModel (Y : ℕ → FiniteModel) : ℕ → FiniteModel
  | 0 => Y 0
  | j + 1 => blockSumModel (prefixModel Y j) (Y (j + 1))

/-- Every prefix model is nonempty as soon as the first model is: the left
summand always embeds. -/
theorem nonempty_prefixModel (Y : ℕ → FiniteModel) (h0 : Nonempty (Y 0)) :
    ∀ j, Nonempty (prefixModel Y j)
  | 0 => h0
  | j + 1 => by
    obtain ⟨y⟩ := nonempty_prefixModel Y h0 j
    exact ⟨Sum.inl y⟩

/-- Prefix models have positive cardinality when the first model does. -/
theorem card_prefixModel_pos (Y : ℕ → FiniteModel) (h0 : Nonempty (Y 0))
    (j : ℕ) : 0 < Fintype.card (prefixModel Y j) := by
  haveI := nonempty_prefixModel Y h0 j
  exact Fintype.card_pos

/-! ## The prefix block diagonals -/

/-- The block diagonal of the first `j + 1` entries of a matrix sequence. -/
def prefixDiag (Y : ℕ → FiniteModel) (x : ∀ n, Matrix (Y n) (Y n) ℂ) :
    ∀ j, Matrix (prefixModel Y j) (prefixModel Y j) ℂ
  | 0 => x 0
  | j + 1 =>
    blockDiagMatrix (prefixModel Y j) (Y (j + 1)) (prefixDiag Y x j) (x (j + 1))

variable (Y : ℕ → FiniteModel) (x y : ∀ n, Matrix (Y n) (Y n) ℂ)

theorem prefixDiag_add : ∀ j,
    prefixDiag Y (fun n ↦ x n + y n) j = prefixDiag Y x j + prefixDiag Y y j
  | 0 => rfl
  | j + 1 => by
    show blockDiagMatrix _ _ (prefixDiag Y (fun n ↦ x n + y n) j)
        (x (j + 1) + y (j + 1)) = _
    rw [prefixDiag_add j]
    exact (MFAlgebraDimension.blockDiagMatrix_add _ _ _ _ _ _).symm

theorem prefixDiag_mul : ∀ j,
    prefixDiag Y (fun n ↦ x n * y n) j = prefixDiag Y x j * prefixDiag Y y j
  | 0 => rfl
  | j + 1 => by
    show blockDiagMatrix _ _ (prefixDiag Y (fun n ↦ x n * y n) j)
        (x (j + 1) * y (j + 1)) = _
    rw [prefixDiag_mul j]
    exact (blockDiagMatrix_mul _ _ _ _ _ _).symm

theorem prefixDiag_smul (z : ℂ) : ∀ j,
    prefixDiag Y (fun n ↦ z • x n) j = z • prefixDiag Y x j
  | 0 => rfl
  | j + 1 => by
    show blockDiagMatrix _ _ (prefixDiag Y (fun n ↦ z • x n) j)
        (z • x (j + 1)) = _
    rw [prefixDiag_smul z j]
    exact (MFAlgebraDimension.blockDiagMatrix_smul _ _ _ _ _).symm

theorem prefixDiag_star : ∀ j,
    prefixDiag Y (fun n ↦ star (x n)) j = star (prefixDiag Y x j)
  | 0 => rfl
  | j + 1 => by
    show blockDiagMatrix _ _ (prefixDiag Y (fun n ↦ star (x n)) j)
        (star (x (j + 1))) = _
    rw [prefixDiag_star j]
    exact (blockDiagMatrix_star _ _ _ _).symm

theorem prefixDiag_zero : ∀ j,
    prefixDiag Y (fun _ ↦ 0) j = (0 : Matrix (prefixModel Y j)
      (prefixModel Y j) ℂ)
  | 0 => rfl
  | j + 1 => by
    show blockDiagMatrix _ _ (prefixDiag Y (fun _ ↦ 0) j) 0 = 0
    rw [prefixDiag_zero j]
    exact MFAlgebraDimension.blockDiagMatrix_zero _ _

end

end ShulmanFill
end GroupApproximation
