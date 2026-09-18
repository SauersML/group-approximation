import GroupApproximation.SteinbergFP.Doubling
import GroupApproximation.SteinbergFP.Diagonal
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Matrix.Mul

/-!
# The Leavitt swap `W₁ ∈ E₃(S)`

For a binary Leavitt family `s₀, s₁, t₀, t₁` of `S`, the matrix

    W₁ = [[t₀, 0, 0], [t₁, 0, 0], [0, s₀, s₁]]

is invertible with inverse `[[s₀, s₁, 0], [0, 0, t₀], [0, 0, t₁]]`, and it is elementary:
with `U = e₀₂(-t₀) e₁₂(-t₁) e₂₀(s₀) e₂₁(s₁)` and `B = e₀₁(-s₀) e₀₂(-s₁)`,

    U · W₁ · B = P = [[0, -1, 0], [0, 0, -1], [1, 0, 0]],

and `P = w₂₁ w₁₀` is a product of Weyl elements `w_{ij} = x_{ij}(1) x_{ji}(-1) x_{ij}(1)`.
So `swap L = U⁻¹ (w₂₁ w₁₀) B⁻¹ ∈ St₃(S)` has elementary matrix `W₁` (`stMatrix_swap`).
This is "Change 1" of the research node `leavitt-pair-centralizers-embed-e-n-in-st-3n-plus-1`
(the elementary factorization of the square swap, with no Whitehead doubling), for `N = 1`.
-/

namespace GroupApproximation.SteinbergFP

noncomputable section

open SteinbergGroup

variable {S : Type*} [Ring S] (L : LeavittFamily S)

/-- The `3 × 3` Leavitt swap matrix. -/
def swapMatrix : Matrix (Fin 3) (Fin 3) S :=
  !![L.t0, 0, 0; L.t1, 0, 0; 0, L.s0, L.s1]

private theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
private theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
private theorem ne12 : (1 : Fin 3) ≠ 2 := by decide

/-- A Weyl element `w_{ij} = x_{ij}(1) x_{ji}(-1) x_{ij}(1)`. -/
def weyl (i j : Fin 3) (h : i ≠ j) : SteinbergGroup (Fin 3) S :=
  x i j h 1 * x j i h.symm (-1) * x i j h 1

/-- `U = e₀₂(-t₀) e₁₂(-t₁) e₂₀(s₀) e₂₁(s₁)`. -/
def swapLeft : SteinbergGroup (Fin 3) S :=
  x 0 2 ne02 (-L.t0) * x 1 2 ne12 (-L.t1) * x 2 0 ne02.symm L.s0 * x 2 1 ne12.symm L.s1

/-- `B = e₀₁(-s₀) e₀₂(-s₁)`. -/
def swapRight : SteinbergGroup (Fin 3) S :=
  x 0 1 ne01 (-L.s0) * x 0 2 ne02 (-L.s1)

/-- The Leavitt swap element of `St₃(S)`. -/
def swap : SteinbergGroup (Fin 3) S :=
  (swapLeft L)⁻¹ * (weyl 2 1 ne12.symm * weyl 1 0 ne01.symm) * (swapRight L)⁻¹

/-- Elementary `3 × 3` matrices as literals. -/
theorem one_add_single_fin3 (i j : Fin 3) (c : S) :
    (1 : Matrix (Fin 3) (Fin 3) S) + Matrix.single i j c =
      Matrix.of fun a b ↦ (if a = b then 1 else 0) + (if a = i ∧ b = j then c else 0) := by
  ext a b
  simp [Matrix.one_apply, Matrix.single_apply, eq_comm]

theorem stMatrix_swapLeft :
    stMatrix (Fin 3) S (swapLeft L) =
      !![1 - L.t0 * L.s0, -(L.t0 * L.s1), -L.t0;
         -(L.t1 * L.s0), 1 - L.t1 * L.s1, -L.t1;
         L.s0, L.s1, 1] := by
  simp only [swapLeft, map_mul, stMatrix_x]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

theorem stMatrix_swapRight :
    stMatrix (Fin 3) S (swapRight L) = !![1, -L.s0, -L.s1; 0, 1, 0; 0, 0, 1] := by
  simp only [swapRight, map_mul, stMatrix_x]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

theorem stMatrix_weyls :
    stMatrix (Fin 3) S (weyl 2 1 ne12.symm * weyl 1 0 ne01.symm) =
      !![0, -1, 0; 0, 0, -1; 1, 0, 0] := by
  simp only [weyl, map_mul, stMatrix_x]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

/-- `U · W₁ · B = P`. -/
theorem swap_factorization :
    stMatrix (Fin 3) S (swapLeft L) * swapMatrix L * stMatrix (Fin 3) S (swapRight L) =
      stMatrix (Fin 3) S (weyl 2 1 ne12.symm * weyl 1 0 ne01.symm) := by
  rw [stMatrix_swapLeft, stMatrix_swapRight, stMatrix_weyls, swapMatrix]
  have h1 : !![1 - L.t0 * L.s0, -(L.t0 * L.s1), -L.t0;
        -(L.t1 * L.s0), 1 - L.t1 * L.s1, -L.t1;
        L.s0, L.s1, 1] * !![L.t0, 0, 0; L.t1, 0, 0; 0, L.s0, L.s1] =
      !![0, -1, 0; 0, 0, -1; 1, L.s0, L.s1] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, L.t0_s0, L.t0_s1, L.t1_s0, L.t1_s1, L.sum_range]
  rw [h1]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- **The swap element has elementary matrix `W₁`.** -/
theorem stMatrix_swap : stMatrix (Fin 3) S (swap L) = swapMatrix L := by
  have hinvU : stMatrix (Fin 3) S (swapLeft L)⁻¹ * stMatrix (Fin 3) S (swapLeft L) = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hinvB : stMatrix (Fin 3) S (swapRight L) * stMatrix (Fin 3) S (swapRight L)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  rw [swap, map_mul, map_mul, ← swap_factorization L]
  calc stMatrix (Fin 3) S (swapLeft L)⁻¹ *
        (stMatrix (Fin 3) S (swapLeft L) * swapMatrix L * stMatrix (Fin 3) S (swapRight L)) *
        stMatrix (Fin 3) S (swapRight L)⁻¹
      = (stMatrix (Fin 3) S (swapLeft L)⁻¹ * stMatrix (Fin 3) S (swapLeft L)) * swapMatrix L *
          (stMatrix (Fin 3) S (swapRight L) * stMatrix (Fin 3) S (swapRight L)⁻¹) := by
        simp only [mul_assoc]
    _ = swapMatrix L := by rw [hinvU, hinvB, one_mul, mul_one]

end

end GroupApproximation.SteinbergFP

#audit_axioms GroupApproximation.SteinbergFP.stMatrix_swap
