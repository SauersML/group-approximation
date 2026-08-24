import GroupApproximation.Leavitt.LeavittMatrixCompression
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# The rank-twelve Leavitt self-compression

`non_mf_groups_exist.tex`, Section~"The binary Leavitt self-compression": the
matrices `X`, `Y`, the compressor `τ = diag(X, Y)` of `eq:tau`, the Whitehead
factorization `eq:whitehead-factorization`, and the corner conjugation
`eq:corner-conjugation`.

## How the twelve coordinates are organised

The manuscript writes `12 × 12` matrices with indices `0, …, 11` and puts the
Kazhdan corner `EL₃` on `{0, 1, 2}`.  Here the same twelve coordinates are
carried as the nested index type

`(Fin 2 × Fin 2) × Fin 3`,   `((a, b), c) ↦ 6a + 3b + c`,

so that the printed block structure is definitional rather than an index
computation:

* the innermost `Fin 3` is the Kazhdan corner, and `Cell A = M₃(A)` is the ring
  the manuscript's `Ψ` acts on;
* the middle `Fin 2` splits each `6 × 6` half into the two `3 × 3` blocks that
  `X` and `Y` are written with, so `Half A = M₂(Cell A) = M₆(A)`;
* the outer `Fin 2` is the `diag(X, Y)` split, so `Full A = M₂(Half A) = M₁₂(A)`.

Every identity below is therefore a `2 × 2` matrix computation.

The manuscript's `Ψ(A) = qI₃ + s₀At₀` is already in the development as
`LeavittFamily.matrixCompression`, together with its multiplicativity,
unitality, injectivity (`matrixCompression_recover`) and its value on
elementary matrices (`matrixCompression_elementaryUnit`).

Nothing here is specific to the binary Leavitt algebra: the arguments use only
`LeavittFamily`, i.e. the relations `t_i s_j = δ_{ij}` and `s₀t₀ + s₁t₁ = 1`.
-/

namespace GroupApproximation
namespace RankTwelve

variable {A : Type*} [Ring A]

/-- `M₃(A)`: the ring carrying the Kazhdan corner and the manuscript's `Ψ`. -/
abbrev Cell (A : Type*) [Ring A] := Matrix (Fin 3) (Fin 3) A

/-- `M₂(M₃(A)) = M₆(A)`: the ring the manuscript writes `X` and `Y` over. -/
abbrev Half (A : Type*) [Ring A] := Matrix (Fin 2) (Fin 2) (Cell A)

/-- `M₂(M₆(A)) = M₁₂(A)`: the ring `τ` lives in. -/
abbrev Full (A : Type*) [Ring A] := Matrix (Fin 2) (Fin 2) (Half A)

/-! ## The scalar embedding `a ↦ a·I₃` -/

/-- The manuscript's `aI₃`. -/
def kap (a : A) : Cell A := Matrix.diagonal fun _ ↦ a

@[simp] theorem kap_mul (a b : A) : (kap a : Cell A) * kap b = kap (a * b) :=
  Matrix.diagonal_mul_diagonal _ _

@[simp] theorem kap_one : (kap (1 : A) : Cell A) = 1 := Matrix.diagonal_one

@[simp] theorem kap_zero : (kap (0 : A) : Cell A) = 0 := Matrix.diagonal_zero

@[simp] theorem kap_add (a b : A) : (kap a : Cell A) + kap b = kap (a + b) := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp [kap, Matrix.diagonal_apply_eq]
  · simp [kap, Matrix.diagonal_apply_ne _ h]

/-- The manuscript's `aI₃` is the development's `scalarDiagonal`. -/
@[simp] theorem scalarDiagonal_eq_kap (a : A) :
    LeavittFamily.scalarDiagonal (ι := Fin 3) a = kap a := rfl

/-! ## `X` and `Y` -/

variable (L : LeavittFamily A)

/-- The manuscript's `X = [[s₀I₃, s₁t₀I₃], [0, t₁I₃]]`. -/
def shift : Half A := !![kap L.s0, kap (L.s1 * L.t0); 0, kap L.t1]

/-- The manuscript's `Y = [[t₀I₃, 0], [s₀t₁I₃, s₁I₃]]`. -/
def shiftInv : Half A := !![kap L.t0, 0; kap (L.s0 * L.t1), kap L.s1]

theorem shift_mul_shiftInv : shift L * shiftInv L = 1 := by
  have h1 : L.s0 * L.t0 + L.p1 = 1 := L.sum_range
  have h2 : L.s1 * L.t0 * L.s1 = 0 := by
    rw [mul_assoc, L.t0_s1, mul_zero]
  have h3 : L.t1 * (L.s0 * L.t1) = 0 := by
    rw [← mul_assoc, L.t1_s0, zero_mul]
  rw [shift, shiftInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [h1, h2, h3]

theorem shiftInv_mul_shift : shiftInv L * shift L = 1 := by
  have h3 : L.s0 * L.t1 * L.s0 = 0 := by
    rw [mul_assoc, L.t1_s0, mul_zero]
  rw [shift, shiftInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [h3]

/-- `X` as a unit of `M₆(A)`, with `Y` as its inverse. -/
def shiftUnit : (Half A)ˣ where
  val := shift L
  inv := shiftInv L
  val_inv := shift_mul_shiftInv L
  inv_val := shiftInv_mul_shift L

@[simp] theorem shiftUnit_val : (shiftUnit L : Half A) = shift L := rfl

@[simp] theorem shiftUnit_inv_val :
    ((shiftUnit L)⁻¹ : (Half A)ˣ).val = shiftInv L := rfl

/-! ## The Kazhdan corner -/

/-- `diag(A, I₃)` inside `M₆(A)`: the upper-left `3 × 3` corner of a half. -/
def halfCorner (M : Cell A) : Half A := !![M, 0; 0, 1]

@[simp] theorem halfCorner_one : halfCorner (1 : Cell A) = 1 := by
  rw [halfCorner, ← Matrix.one_fin_two]

theorem halfCorner_mul (M N : Cell A) :
    halfCorner M * halfCorner N = halfCorner (M * N) := by
  rw [halfCorner, halfCorner, halfCorner, Matrix.mul_fin_two]
  simp

/-- **`eq:corner-conjugation`, the essential computation.**  Conjugating the
`3 × 3` corner of a half by `X` applies the manuscript's compression `Ψ`. -/
theorem shift_halfCorner_shiftInv (M : Cell A) :
    shift L * halfCorner M * shiftInv L = halfCorner (L.matrixCompression M) := by
  have hcomp : L.matrixCompression M
      = kap L.s0 * M * kap L.t0 + kap L.p1 := by
    rw [LeavittFamily.matrixCompression]
    exact add_comm _ _
  have hq : L.s1 * L.t0 * (L.s0 * L.t1) = L.p1 := by
    rw [mul_assoc, ← mul_assoc L.t0, L.t0_s0, one_mul, LeavittFamily.p1]
  have hz1 : L.s1 * L.t0 * L.s1 = 0 := by
    rw [mul_assoc, L.t0_s1, mul_zero]
  have hz2 : L.t1 * (L.s0 * L.t1) = 0 := by
    rw [← mul_assoc, L.t1_s0, zero_mul]
  rw [shift, shiftInv, halfCorner, halfCorner, hcomp, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  simp [hq, hz1, hz2]

/-! ## `τ = diag(X, Y)` and its Whitehead factorization -/

/-- The manuscript's `τ = diag(X, Y)` in `eq:tau`. -/
def tau : Full A := !![shift L, 0; 0, shiftInv L]

/-- `τ⁻¹ = diag(Y, X)`. -/
def tauInv : Full A := !![shiftInv L, 0; 0, shift L]

theorem tau_mul_tauInv : tau L * tauInv L = 1 := by
  rw [tau, tauInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [shift_mul_shiftInv, shiftInv_mul_shift]

theorem tauInv_mul_tau : tauInv L * tau L = 1 := by
  rw [tau, tauInv, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp [shift_mul_shiftInv, shiftInv_mul_shift]

/-- `τ` as a unit of `M₁₂(A)`. -/
def tauUnit : (Full A)ˣ where
  val := tau L
  inv := tauInv L
  val_inv := tau_mul_tauInv L
  inv_val := tauInv_mul_tau L

@[simp] theorem tauUnit_val : (tauUnit L : Full A) = tau L := rfl

@[simp] theorem tauUnit_inv_val :
    ((tauUnit L)⁻¹ : (Full A)ˣ).val = tauInv L := rfl

/-- The block-unipotent `[[I, N], [0, I]]` of `eq:whitehead-factorization`. -/
def upperBlock (N : Half A) : Full A := !![1, N; 0, 1]

/-- The block-unipotent `[[I, 0], [N, I]]` of `eq:whitehead-factorization`. -/
def lowerBlock (N : Half A) : Full A := !![1, 0; N, 1]

/-- The first three factors of `eq:whitehead-factorization` collapse to the
Whitehead word `w(X)`. -/
theorem whitehead_upper :
    upperBlock (shift L) * lowerBlock (-shiftInv L) * upperBlock (shift L)
      = !![0, shift L; -shiftInv L, 0] := by
  simp only [upperBlock, lowerBlock]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [shift_mul_shiftInv, shiftInv_mul_shift]

/-- The last three factors of `eq:whitehead-factorization` collapse to
`w(-1)`. -/
theorem whitehead_lower :
    lowerBlock (1 : Half A) * upperBlock (-1) * lowerBlock 1
      = !![0, -1; 1, 0] := by
  simp only [upperBlock, lowerBlock]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp

/-- **`eq:whitehead-factorization`.**  `diag(X, X⁻¹)` is the printed product of
six block-unipotent factors, so `τ` is a product of elementary matrices. -/
theorem tau_eq_whitehead_product :
    tau L =
      upperBlock (shift L) * lowerBlock (-shiftInv L) * upperBlock (shift L) *
        lowerBlock 1 * upperBlock (-1) * lowerBlock 1 := by
  have hgroup :
      upperBlock (shift L) * lowerBlock (-shiftInv L) * upperBlock (shift L) *
          lowerBlock 1 * upperBlock (-1) * lowerBlock 1
        = (upperBlock (shift L) * lowerBlock (-shiftInv L) *
            upperBlock (shift L)) *
          (lowerBlock (1 : Half A) * upperBlock (-1) * lowerBlock 1) := by
    simp [mul_assoc]
  rw [hgroup, whitehead_upper, whitehead_lower, tau, Matrix.mul_fin_two]
  simp

/-! ## The corner of the whole `12 × 12` matrix -/

/-- `diag(A, I₉)`: the manuscript's identification of `M₃(A)` with the
upper-left corner of `M₁₂(A)`. -/
def fullCorner (M : Cell A) : Full A := !![halfCorner M, 0; 0, 1]

@[simp] theorem fullCorner_one : fullCorner (1 : Cell A) = 1 := by
  rw [fullCorner, halfCorner_one, ← Matrix.one_fin_two]

theorem fullCorner_mul (M N : Cell A) :
    fullCorner M * fullCorner N = fullCorner (M * N) := by
  rw [fullCorner, fullCorner, fullCorner, Matrix.mul_fin_two]
  simp [halfCorner_mul]

/-- **`eq:corner-conjugation`.**  `τ diag(A, I₉) τ⁻¹ = diag(Ψ(A), I₉)`. -/
theorem tau_fullCorner_tauInv (M : Cell A) :
    tau L * fullCorner M * tauInv L = fullCorner (L.matrixCompression M) := by
  rw [tau, tauInv, fullCorner, fullCorner, Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  simp [shift_halfCorner_shiftInv, shiftInv_mul_shift]

end RankTwelve
end GroupApproximation
