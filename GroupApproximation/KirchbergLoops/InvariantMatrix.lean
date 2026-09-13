import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Matrix.Block

/-!
# The invariant matrix of the six Kirchberg circle loops

For the unital UCT Kirchberg algebra `A = B ⊗ B` of the STW Problem L artifact
(`research/artifacts/stw50-six-kirchberg-loops-2026-09-05.md`), the invariant
`Δ : π₁(Aut A, id) → Hom(K₁(A), K₀(A)) ⊕ Hom(K₀(A)/ℤ[1_A], K₁(A))` takes values in `ℤ⁶`, with
coordinates `((Δx)_e, (Δx)_β, (Δy)_e, (Δy)_β, (Δβ)_x, (Δβ)_y)`. This file proves the integer part of
Theorem 3 and §7 of that artifact: the columns of the matrix `L` of (15) are a `ℤ`-basis of `ℤ⁶`.

Only integer linear algebra is proved here. That `Δ` is an isomorphism (Dadarlat, Theorem 6.3), and
that the six loops have these columns (graph K-theory, Künneth, classification), are not formalized.

* `invariantMatrix`: `L = fromBlocks 1 X 0 J`, indexed by `Fin 4 ⊕ Fin 2`.
* `reindex_invariantMatrix`: after `finSumFinEquiv`, `L` is the printed 6×6 matrix (15).
* `det_invariantMatrix`: `det L = 1`.
* `invariantMatrix_mul_inv`, `inv_mul_invariantMatrix`: the explicit inverse.
* `loopBasis`: the columns of `L` as a basis of `Fin 4 ⊕ Fin 2 → ℤ`.
* `loopBasis_repr`: the coefficient formula (16), `(a - g, b, c + f, d, g, -f)`.
* `kernelColumn_span`: the four kernel columns (18) span the classes with `(Δx)_e = (Δy)_e = 0`.
-/

namespace GroupApproximation
namespace KirchbergLoops

open Matrix

/-- The coordinate index. `Sum.inl 0, 1, 2, 3` are `(Δx)_e, (Δx)_β, (Δy)_e, (Δy)_β`, the summand
`Hom(K₁(A), K₀(A))`. `Sum.inr 0, 1` are `(Δβ)_x, (Δβ)_y`, the summand `Hom(K₀(A)/ℤe, K₁(A))`. As a
column index, `Sum.inl j` is the loop `σ_{j+1}`, `Sum.inr 0` is `ρ₁` and `Sum.inr 1` is `ρ₂`. -/
abbrev Coord := Fin 4 ⊕ Fin 2

/-- The `Hom(K₁, K₀)` components of `ρ₁` (`x ↦ e`) and `ρ₂` (`y ↦ e`). -/
def rotationBlock : Matrix (Fin 4) (Fin 2) ℤ := !![1, 0; 0, 0; 0, 1; 0, 0]

/-- The `Hom(K₀/ℤe, K₁)` components of `ρ₁` (`β ↦ y`) and `ρ₂` (`β ↦ -x`). -/
def rotationQuotientBlock : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

/-- The inverse of `rotationQuotientBlock`. -/
def rotationQuotientBlockInv : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- **The invariant matrix `L` of (15).** Its columns are the invariants of `σ₁, σ₂, σ₃, σ₄, ρ₁, ρ₂`. -/
def invariantMatrix : Matrix Coord Coord ℤ := fromBlocks 1 rotationBlock 0 rotationQuotientBlock

/-- The explicit inverse of `invariantMatrix`. -/
def invariantMatrixInv : Matrix Coord Coord ℤ :=
  fromBlocks 1 (-(rotationBlock * rotationQuotientBlockInv)) 0 rotationQuotientBlockInv

/-- **`L` is the printed matrix (15).** -/
theorem reindex_invariantMatrix :
    reindex finSumFinEquiv finSumFinEquiv invariantMatrix =
      !![1, 0, 0, 0, 1, 0;
         0, 1, 0, 0, 0, 0;
         0, 0, 1, 0, 0, 1;
         0, 0, 0, 1, 0, 0;
         0, 0, 0, 0, 0, -1;
         0, 0, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **`det L = 1`.** -/
theorem det_invariantMatrix : invariantMatrix.det = 1 := by
  rw [invariantMatrix, det_fromBlocks_zero₂₁, det_one, rotationQuotientBlock, det_fin_two_of]
  norm_num

theorem rotationQuotientBlock_mul_inv : rotationQuotientBlock * rotationQuotientBlockInv = 1 := by
  rw [rotationQuotientBlock, rotationQuotientBlockInv, mul_fin_two, one_fin_two]
  norm_num

theorem inv_mul_rotationQuotientBlock : rotationQuotientBlockInv * rotationQuotientBlock = 1 := by
  rw [rotationQuotientBlock, rotationQuotientBlockInv, mul_fin_two, one_fin_two]
  norm_num

theorem invariantMatrix_mul_inv : invariantMatrix * invariantMatrixInv = 1 := by
  rw [invariantMatrix, invariantMatrixInv, fromBlocks_multiply, rotationQuotientBlock_mul_inv]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    neg_add_cancel, fromBlocks_one]

theorem inv_mul_invariantMatrix : invariantMatrixInv * invariantMatrix = 1 := by
  rw [invariantMatrix, invariantMatrixInv, fromBlocks_multiply, inv_mul_rotationQuotientBlock]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.neg_mul, Matrix.mul_assoc, inv_mul_rotationQuotientBlock, add_neg_cancel, fromBlocks_one]

/-- The linear equivalence `v ↦ L⁻¹ v` from invariant coordinates to loop coefficients. -/
def coefficientEquiv : (Coord → ℤ) ≃ₗ[ℤ] (Coord → ℤ) :=
  LinearEquiv.ofLinear (mulVecLin invariantMatrixInv) (mulVecLin invariantMatrix)
    (by rw [← Matrix.mulVecLin_mul, inv_mul_invariantMatrix, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, invariantMatrix_mul_inv, Matrix.mulVecLin_one])

/-- **The six loop columns form a `ℤ`-basis of `ℤ⁶`.** -/
noncomputable def loopBasis : Module.Basis Coord ℤ (Coord → ℤ) := Module.Basis.ofEquivFun coefficientEquiv

theorem loopBasis_apply (j : Coord) : loopBasis j = invariantMatrix.col j := by
  rw [loopBasis, Module.Basis.coe_ofEquivFun]
  exact mulVec_single_one invariantMatrix j

/-- The coefficients `(a - g, b, c + f, d, g, -f)` of (16), for coordinates `(a, b, c, d, f, g)`. -/
def coefficients (v : Coord → ℤ) : Coord → ℤ :=
  Sum.elim ![v (.inl 0) - v (.inr 1), v (.inl 1), v (.inl 2) + v (.inr 0), v (.inl 3)]
    ![v (.inr 1), -v (.inr 0)]

/-- Every coordinate vector is `L` applied to its coefficients (16). -/
theorem invariantMatrix_mulVec_coefficients (v : Coord → ℤ) :
    invariantMatrix *ᵥ coefficients v = v := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [invariantMatrix, rotationBlock, rotationQuotientBlock, coefficients, Matrix.mulVec,
      dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]

/-- **The coefficient formula (16).** The coordinates of `v` in the loop basis are
`(a - g, b, c + f, d, g, -f)`. -/
theorem loopBasis_repr (v : Coord → ℤ) (j : Coord) : loopBasis.repr v j = coefficients v j := by
  have h : invariantMatrixInv *ᵥ v = coefficients v := by
    conv_lhs => rw [← invariantMatrix_mulVec_coefficients v]
    rw [Matrix.mulVec_mulVec, inv_mul_invariantMatrix, Matrix.one_mulVec]
  rw [loopBasis, Module.Basis.ofEquivFun_repr_apply]
  exact congrFun h j

/-- The columns (18) of the kernel loops `κ₁ = σ₂`, `κ₂ = σ₄`, `κ₃ = ρ₁σ₁⁻¹`, `κ₄ = ρ₂σ₃⁻¹`. -/
def kernelColumn : Fin 4 → Coord → ℤ :=
  ![invariantMatrix.col (.inl 1), invariantMatrix.col (.inl 3),
    invariantMatrix.col (.inr 0) - invariantMatrix.col (.inl 0),
    invariantMatrix.col (.inr 1) - invariantMatrix.col (.inl 2)]

/-- **The kernel columns (18).** -/
theorem kernelColumn_eq :
    kernelColumn = ![Sum.elim ![0, 1, 0, 0] ![0, 0], Sum.elim ![0, 0, 0, 1] ![0, 0],
      Sum.elim ![0, 0, 0, 0] ![0, 1], Sum.elim ![0, 0, 0, 0] ![-1, 0]] := by
  funext k i
  fin_cases k <;> rcases i with i | i <;> fin_cases i <;> rfl

/-- **The kernel loops (17) span the classes with `(Δx)_e = (Δy)_e = 0`.** For such a class with
coordinates `(0, b, 0, d, f, g)`, it is `b κ₁ + d κ₂ + g κ₃ - f κ₄`. -/
theorem kernelColumn_span (v : Coord → ℤ) (hx : v (.inl 0) = 0) (hy : v (.inl 2) = 0) :
    v = v (.inl 1) • kernelColumn 0 + v (.inl 3) • kernelColumn 1 + v (.inr 1) • kernelColumn 2 -
      v (.inr 0) • kernelColumn 3 := by
  rw [kernelColumn_eq]
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [hx, hy]

end KirchbergLoops
end GroupApproximation
