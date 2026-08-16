import GroupApproximation.Sofic.KazhdanCornerModel

/-!
# Operator norms of amplified block patterns

Section 49.1 builds the induced representation as a *block-monomial* matrix over
`Fin m × Y`: one nonzero block per column-block, placed by a permutation of the
coset index.  Two norm facts carry the whole construction.

* `l2_opNorm_monomialBlocks_le` — a block-monomial matrix is no larger than its
  largest block.  This is what makes the multiplicative defect of an induced
  representation the maximum of the defects of the inducing one.
* `l2_opNorm_block_le` — a diagonal block is no larger than the whole matrix.
  This is what lets the base block of an induced representation be read back.

Both are proved by the elementary vector criterion of `Sofic.KazhdanCornerModel`,
so no `EuclideanSpace` bookkeeping leaks into the induction argument.
-/

namespace GroupApproximation

namespace AmplifiedBlocks

open Matrix KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

/-- The amplified coordinate model: `m` copies of `Y`. -/
@[reducible] def ampModel (m : ℕ) (Y : FiniteModel) : FiniteModel where
  carrier := Fin m × Y.carrier
  fintype := inferInstance
  decidableEq := inferInstance

variable {m : ℕ} {Y : FiniteModel}

/-- **Block-monomial bound.**  A matrix whose only nonzero blocks are `E j`,
placed in row-block `τ j` of column-block `j`, has norm at most the largest
block norm. -/
theorem l2_opNorm_monomialBlocks_le (τ : Equiv.Perm (Fin m))
    (E : Fin m → Matrix Y Y ℂ) {M : ℝ} (hM : 0 ≤ M) (hE : ∀ j, ‖E j‖ ≤ M)
    (D : Matrix (ampModel m Y) (ampModel m Y) ℂ)
    (hD : ∀ p q : Fin m × Y.carrier,
      D p q = if τ q.1 = p.1 then E q.1 p.2 q.2 else 0) :
    ‖D‖ ≤ M := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general D hM fun v => ?_
  -- the value in row-block `i` comes from column-block `τ⁻¹ i`
  have hval : ∀ p : Fin m × Y.carrier,
      (D *ᵥ v) p = (E (τ.symm p.1) *ᵥ (fun y => v (τ.symm p.1, y))) p.2 := by
    intro p
    rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (τ.symm p.1)]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [hD]
      simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hD]
      have hne : τ j ≠ p.1 := by
        intro hcon
        exact hj (by rw [← hcon, Equiv.symm_apply_apply])
      rw [if_neg hne, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hsum : ∑ p : Fin m × Y.carrier, Complex.normSq ((D *ᵥ v) p)
      = ∑ j : Fin m, ∑ y : Y.carrier,
          Complex.normSq ((E j *ᵥ (fun z => v (j, z))) y) := by
    rw [Fintype.sum_prod_type]
    refine Fintype.sum_equiv τ.symm _ _ fun i => ?_
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hval (i, y)]
  rw [hsum]
  have hbound : ∀ j : Fin m,
      ∑ y : Y.carrier, Complex.normSq ((E j *ᵥ (fun z => v (j, z))) y)
        ≤ M ^ 2 * ∑ y : Y.carrier, Complex.normSq (v (j, y)) := by
    intro j
    refine le_trans (sum_normSq_mulVec_le_general (E j) _) ?_
    have hEj : ‖E j‖ ^ 2 ≤ M ^ 2 := by
      have := hE j
      nlinarith [norm_nonneg (E j)]
    have hnn : 0 ≤ ∑ y : Y.carrier, Complex.normSq (v (j, y)) :=
      Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _
    exact mul_le_mul_of_nonneg_right hEj hnn
  calc ∑ j : Fin m, ∑ y : Y.carrier,
        Complex.normSq ((E j *ᵥ (fun z => v (j, z))) y)
      ≤ ∑ j : Fin m, M ^ 2 * ∑ y : Y.carrier, Complex.normSq (v (j, y)) :=
        Finset.sum_le_sum fun j _ => hbound j
    _ = M ^ 2 * ∑ p : Fin m × Y.carrier, Complex.normSq (v p) := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type]

/-- **Block bound.**  A diagonal block of a matrix is no larger than the
matrix. -/
theorem l2_opNorm_block_le (i₀ : Fin m)
    (A : Matrix (ampModel m Y) (ampModel m Y) ℂ) :
    ‖A.submatrix (fun y : Y.carrier => ((i₀, y) : Fin m × Y.carrier))
      (fun y : Y.carrier => ((i₀, y) : Fin m × Y.carrier))‖ ≤ ‖A‖ := by
  classical
  refine l2_opNorm_le_of_sum_normSq_general _ (norm_nonneg A) fun v => ?_
  set w : Fin m × Y.carrier → ℂ :=
    fun p => if p.1 = i₀ then v p.2 else 0 with hw
  have hval : ∀ y : Y.carrier,
      (A.submatrix (fun z : Y.carrier => ((i₀, z) : Fin m × Y.carrier))
        (fun z : Y.carrier => ((i₀, z) : Fin m × Y.carrier)) *ᵥ v) y
      = (A *ᵥ w) (i₀, y) := by
    intro y
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single i₀]
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [hw]
      simp [Matrix.submatrix_apply]
    · intro j _ hj
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [hw]
      simp [hj]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hle : ∑ y : Y.carrier, Complex.normSq
        ((A.submatrix (fun z : Y.carrier => ((i₀, z) : Fin m × Y.carrier))
          (fun z : Y.carrier => ((i₀, z) : Fin m × Y.carrier)) *ᵥ v) y)
      ≤ ∑ p : Fin m × Y.carrier, Complex.normSq ((A *ᵥ w) p) := by
    rw [Fintype.sum_prod_type]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun y _ => by rw [hval y]))
      ?_
    refine Finset.single_le_sum (f := fun j : Fin m =>
      ∑ y : Y.carrier, Complex.normSq ((A *ᵥ w) (j, y))) ?_ (Finset.mem_univ i₀)
    intro j _
    exact Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _
  refine le_trans hle (le_trans (sum_normSq_mulVec_le_general A w) ?_)
  have hwsum : ∑ p : Fin m × Y.carrier, Complex.normSq (w p)
      = ∑ y : Y.carrier, Complex.normSq (v y) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single i₀]
    · refine Finset.sum_congr rfl fun y _ => ?_
      rw [hw]
      simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [hw]
      simp [hj]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  rw [hwsum]

end AmplifiedBlocks

end GroupApproximation
