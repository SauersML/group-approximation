import GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.PowersStormerGram
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-26, part 4: `2 × 2` block matrices for the Hermitian doubling

These are block-matrix helpers on `m ⊕ m`:

* subtraction, trace and positivity of block matrices;
* rectangular isometries have operator norm at most `1`, so the off-diagonal blocks of a
  contraction are contractions;
* the `(1,2)` block's squared Hilbert--Schmidt norm is at most that of the whole matrix;
* the commutator of the doubling `[[0, y], [yᴴ, 0]]` with `diag(T, T)`, and the trace of an
  off-diagonal block matrix times `G`.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.NuclearDensity

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

noncomputable section

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Block matrices subtract blockwise. -/
theorem powersStormer_fromBlocks_sub (A B C D A' B' C' D' : Matrix m m ℂ) :
    fromBlocks A B C D - fromBlocks A' B' C' D'
      = fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext (i | i) (j | j) <;> simp

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_fromBlocks_sub

/-- The trace of a block matrix is the sum of the traces of its diagonal blocks. -/
theorem powersStormer_trace_fromBlocks (P Q R S : Matrix m m ℂ) :
    trace (fromBlocks P Q R S) = trace P + trace S := by
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₂₂]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_trace_fromBlocks

/-- A block-diagonal matrix with positive semidefinite blocks is positive semidefinite. -/
theorem powersStormer_posSemidef_fromBlocks {P Q : Matrix m m ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : (fromBlocks P 0 0 Q).PosSemidef := by
  have e : fromBlocks P 0 0 Q
      = (fromCols (1 : Matrix m m ℂ) (0 : Matrix m m ℂ))ᴴ * P
          * fromCols (1 : Matrix m m ℂ) (0 : Matrix m m ℂ)
        + (fromCols (0 : Matrix m m ℂ) (1 : Matrix m m ℂ))ᴴ * Q
          * fromCols (0 : Matrix m m ℂ) (1 : Matrix m m ℂ) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_fromCols, mul_fromCols,
      conjTranspose_fromCols_eq_fromRows_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
      fromRows_mul_fromCols, fromBlocks_add]
    simp only [conjTranspose_one, conjTranspose_zero, one_mul, zero_mul, mul_one, mul_zero,
      add_zero, zero_add]
  rw [e]
  exact (hP.conjTranspose_mul_mul_same _).add (hQ.conjTranspose_mul_mul_same _)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_posSemidef_fromBlocks

/-- A rectangular isometry `VᴴV = 1` has operator norm at most `1`. -/
theorem powersStormer_norm_le_one_of_isometry {p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq q] (V : Matrix p q ℂ) (hV : Vᴴ * V = 1) : ‖V‖ ≤ 1 := by
  have h2 : ‖V‖ * ‖V‖ ≤ 1 := by
    rw [← l2_opNorm_conjTranspose_mul_self V, hV]
    exact powersStormer_norm_one_le
  nlinarith [norm_nonneg V, h2]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_le_one_of_isometry

/-- A row-partitioned matrix `[A; B]` with `AᴴA + BᴴB = 1` is a contraction. -/
theorem powersStormer_norm_fromRows_le (A B : Matrix m m ℂ) (h : Aᴴ * A + Bᴴ * B = 1) :
    ‖fromRows A B‖ ≤ 1 := by
  refine powersStormer_norm_le_one_of_isometry _ ?_
  rw [conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows, h]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_fromRows_le

/-- A column-partitioned matrix `[A, B]` with `AAᴴ + BBᴴ = 1` is a contraction. -/
theorem powersStormer_norm_fromCols_le (A B : Matrix m m ℂ) (h : A * Aᴴ + B * Bᴴ = 1) :
    ‖fromCols A B‖ ≤ 1 := by
  rw [← l2_opNorm_conjTranspose (fromCols A B)]
  refine powersStormer_norm_le_one_of_isometry _ ?_
  rw [conjTranspose_conjTranspose, conjTranspose_fromCols_eq_fromRows_conjTranspose,
    fromCols_mul_fromRows, h]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_fromCols_le

/-- The `(2,1)` block of a contraction is a contraction. -/
theorem powersStormer_norm_toBlocks₂₁_le {G : Matrix (m ⊕ m) (m ⊕ m) ℂ} (hG : ‖G‖ ≤ 1) :
    ‖toBlocks₂₁ G‖ ≤ 1 := by
  have e : fromCols (0 : Matrix m m ℂ) (1 : Matrix m m ℂ) * G
      * fromRows (1 : Matrix m m ℂ) (0 : Matrix m m ℂ) = toBlocks₂₁ G := by
    conv_lhs => rw [← fromBlocks_toBlocks G]
    rw [fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp only [zero_mul, zero_add, one_mul, mul_one, mul_zero, add_zero]
  have hR : ‖fromCols (0 : Matrix m m ℂ) (1 : Matrix m m ℂ)‖ ≤ 1 :=
    powersStormer_norm_fromCols_le _ _ (by
      rw [conjTranspose_zero, conjTranspose_one, mul_zero, zero_add, mul_one])
  have hC : ‖fromRows (1 : Matrix m m ℂ) (0 : Matrix m m ℂ)‖ ≤ 1 :=
    powersStormer_norm_fromRows_le _ _ (by
      rw [conjTranspose_zero, conjTranspose_one, mul_zero, add_zero, mul_one])
  rw [← e]
  exact (l2_opNorm_mul _ _).trans
    (mul_le_one₀ ((l2_opNorm_mul _ _).trans (mul_le_one₀ hR (norm_nonneg _) hG))
      (norm_nonneg _) hC)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_toBlocks₂₁_le

/-- The `(1,2)` block of a contraction is a contraction. -/
theorem powersStormer_norm_toBlocks₁₂_le {G : Matrix (m ⊕ m) (m ⊕ m) ℂ} (hG : ‖G‖ ≤ 1) :
    ‖toBlocks₁₂ G‖ ≤ 1 := by
  have e : fromCols (1 : Matrix m m ℂ) (0 : Matrix m m ℂ) * G
      * fromRows (0 : Matrix m m ℂ) (1 : Matrix m m ℂ) = toBlocks₁₂ G := by
    conv_lhs => rw [← fromBlocks_toBlocks G]
    rw [fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    simp only [zero_mul, zero_add, one_mul, mul_one, mul_zero, add_zero]
  have hR : ‖fromCols (1 : Matrix m m ℂ) (0 : Matrix m m ℂ)‖ ≤ 1 :=
    powersStormer_norm_fromCols_le _ _ (by
      rw [conjTranspose_zero, conjTranspose_one, mul_zero, add_zero, mul_one])
  have hC : ‖fromRows (0 : Matrix m m ℂ) (1 : Matrix m m ℂ)‖ ≤ 1 :=
    powersStormer_norm_fromRows_le _ _ (by
      rw [conjTranspose_zero, conjTranspose_one, mul_zero, zero_add, mul_one])
  rw [← e]
  exact (l2_opNorm_mul _ _).trans
    (mul_le_one₀ ((l2_opNorm_mul _ _).trans (mul_le_one₀ hR (norm_nonneg _) hG))
      (norm_nonneg _) hC)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_norm_toBlocks₁₂_le

/-- The `(1,2)` block has squared Hilbert--Schmidt norm at most that of the whole matrix. -/
theorem powersStormer_re_trace_gram_toBlocks₁₂_le (M : Matrix (m ⊕ m) (m ⊕ m) ℂ) :
    (trace ((toBlocks₁₂ M)ᴴ * toBlocks₁₂ M)).re ≤ (trace (Mᴴ * M)).re := by
  rw [ConnesTrick.re_trace_conjTranspose_mul_self, ConnesTrick.re_trace_conjTranspose_mul_self]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, Matrix.toBlocks₁₂, Matrix.of_apply]
  have hA : 0 ≤ ∑ i, ∑ j, Complex.normSq (M (Sum.inl i) (Sum.inl j)) :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
  have hC : 0 ≤ ∑ i, ∑ j, Complex.normSq (M (Sum.inr i) (Sum.inl j)) :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
  have hD : 0 ≤ ∑ i, ∑ j, Complex.normSq (M (Sum.inr i) (Sum.inr j)) :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
  linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_re_trace_gram_toBlocks₁₂_le

/-- The commutator of the Hermitian doubling `[[0, y], [yᴴ, 0]]` with `diag(T, T)`. -/
theorem powersStormer_doubling_commutator (y T : Matrix m m ℂ) :
    fromBlocks 0 y yᴴ 0 * fromBlocks T 0 0 T - fromBlocks T 0 0 T * fromBlocks 0 y yᴴ 0
      = fromBlocks 0 (y * T - T * y) (yᴴ * T - T * yᴴ) 0 := by
  rw [fromBlocks_multiply, fromBlocks_multiply, powersStormer_fromBlocks_sub]
  simp only [zero_mul, mul_zero, add_zero, zero_add, sub_zero]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_doubling_commutator

/-- The trace of an off-diagonal block matrix times `G` pairs each block with the opposite
block of `G`. -/
theorem powersStormer_trace_offdiag_mul (A B : Matrix m m ℂ) (G : Matrix (m ⊕ m) (m ⊕ m) ℂ) :
    trace (fromBlocks 0 A B 0 * G) = trace (A * toBlocks₂₁ G) + trace (B * toBlocks₁₂ G) := by
  conv_lhs => rw [← fromBlocks_toBlocks G]
  rw [fromBlocks_multiply, powersStormer_trace_fromBlocks]
  simp only [zero_mul, zero_add, add_zero]

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.NuclearDensity.powersStormer_trace_offdiag_mul

end

end Manuscript.NonMF.TWWLanes.NuclearDensity
end GroupApproximation
