import GroupApproximation.Sofic.KazhdanCornerModel

/-!
# Block matrices with a partial-permutation support pattern

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378), finite-index half of the cyclic extension step
(Ozawa--Rørdam--Sato, GAFA 25 (2015), §3: induction from a finite-index
normal subgroup).

A matrix on `I × W` is given by its blocks `A i j : Matrix W W ℂ`. The
induced representation of a finite-index subgroup is such a matrix. In each
row and each column of blocks it has at most one nonzero block, so its
operator norm is the maximum of the block norms. This file proves that bound
(`norm_blockMat_le`), together with the algebra of block matrices: product,
difference, conjugate transpose and trace.
-/

namespace GroupApproximation.Full.TWWCyclic

open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-- The matrix on `I × W` whose `(i, j)` block is `A i j`. -/
def blockMat {I W : Type} (A : I → I → Matrix W W ℂ) : Matrix (I × W) (I × W) ℂ :=
  Matrix.of fun p q => A p.1 q.1 p.2 q.2

theorem blockMat_apply {I W : Type} (A : I → I → Matrix W W ℂ) (p q : I × W) :
    blockMat A p q = A p.1 q.1 p.2 q.2 :=
  rfl

/-- Block matrices multiply blockwise. -/
theorem blockMat_mul {I W : Type} [Fintype I] [Fintype W] (A B : I → I → Matrix W W ℂ) :
    blockMat A * blockMat B = blockMat fun i j => ∑ l, A i l * B l j := by
  ext p q
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, blockMat_apply, Matrix.sum_apply]

theorem blockMat_sub {I W : Type} (A B : I → I → Matrix W W ℂ) :
    blockMat A - blockMat B = blockMat fun i j => A i j - B i j := by
  ext p q
  rfl

theorem blockMat_conjTranspose {I W : Type} (A : I → I → Matrix W W ℂ) :
    (blockMat A)ᴴ = blockMat fun i j => (A j i)ᴴ := by
  ext p q
  rfl

/-- The trace of a block matrix is the sum of the traces of its diagonal blocks. -/
theorem trace_blockMat {I W : Type} [Fintype I] [Fintype W] (A : I → I → Matrix W W ℂ) :
    Matrix.trace (blockMat A) = ∑ i, Matrix.trace (A i i) := by
  show ∑ p : I × W, blockMat A p p = ∑ i, ∑ a, A i i a a
  exact Fintype.sum_prod_type _

/-- A row of a block matrix applied to a vector. -/
theorem blockMat_mulVec_apply {I W : Type} [Fintype I] [Fintype W]
    (A : I → I → Matrix W W ℂ) (x : I × W → ℂ) (i : I) (a : W) :
    (blockMat A *ᵥ x) (i, a) = ∑ j, (A i j *ᵥ fun b => x (j, b)) a := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockMat_apply]

/-- A sum of a constant over a set of indices with at most one element. -/
theorem sum_ite_le_of_subsingleton {ι : Type} [Fintype ι] (Q : ι → Prop) [DecidablePred Q]
    {v : ℝ} (hv : 0 ≤ v) (hQ : ∀ i i', Q i → Q i' → i = i') :
    (∑ i, if Q i then v else 0) ≤ v := by
  by_cases h : ∃ i₀, Q i₀
  · obtain ⟨i₀, hi₀⟩ := h
    have hsum : (∑ i, if Q i then v else 0) = if Q i₀ then v else 0 :=
      Finset.sum_eq_single i₀ (fun i _ hi => if_neg fun hq => hi (hQ i i₀ hq hi₀))
        (fun hn => absurd (Finset.mem_univ i₀) hn)
    exact (hsum.trans (if_pos hi₀)).le
  · have hz : (∑ i, if Q i then v else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => if_neg fun hq => h ⟨i, hq⟩
    rw [hz]
    exact hv

/-- **Row bound.** If a row of blocks has at most one nonzero block, the squared norm of
that row of `blockMat A *ᵥ x` is bounded by the squared block bound times the squared
norm of the matching column of `x`. -/
theorem sum_normSq_blockMat_mulVec_row_le {I W : Type} [Fintype I] [Fintype W]
    [DecidableEq W] (A : I → I → Matrix W W ℂ) (P : I → I → Prop) [DecidableRel P]
    {c : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ c) (hP : ∀ i j, A i j ≠ 0 → P i j)
    (hrow : ∀ i j j', P i j → P i j' → j = j') (x : I × W → ℂ) (i : I) :
    ∑ a, Complex.normSq ((blockMat A *ᵥ x) (i, a)) ≤
      ∑ j, if P i j then c ^ 2 * ∑ b, Complex.normSq (x (j, b)) else 0 := by
  by_cases h : ∃ j₀, P i j₀
  · obtain ⟨j₀, hj₀⟩ := h
    have hzero : ∀ j, j ≠ j₀ → A i j = 0 := fun j hj => by
      by_contra hne
      exact hj (hrow i j j₀ (hP i j hne) hj₀)
    have hrowv : ∀ a, (blockMat A *ᵥ x) (i, a) = (A i j₀ *ᵥ fun b => x (j₀, b)) a := by
      intro a
      rw [blockMat_mulVec_apply]
      refine Finset.sum_eq_single j₀ (fun j _ hj => ?_)
        (fun hn => absurd (Finset.mem_univ j₀) hn)
      rw [hzero j hj, Matrix.zero_mulVec, Pi.zero_apply]
    have hnn : ∀ j, 0 ≤ if P i j then c ^ 2 * ∑ b, Complex.normSq (x (j, b)) else 0 :=
      fun j => ite_nonneg (mul_nonneg (sq_nonneg c)
        (Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)) le_rfl
    calc ∑ a, Complex.normSq ((blockMat A *ᵥ x) (i, a))
        = ∑ a, Complex.normSq ((A i j₀ *ᵥ fun b => x (j₀, b)) a) :=
          Finset.sum_congr rfl fun a _ => by rw [hrowv a]
      _ ≤ ‖A i j₀‖ ^ 2 * ∑ b, Complex.normSq (x (j₀, b)) :=
          KazhdanCornerMatrices.sum_normSq_mulVec_le_general (A i j₀) _
      _ ≤ c ^ 2 * ∑ b, Complex.normSq (x (j₀, b)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hA i j₀) 2)
            (Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)
      _ = if P i j₀ then c ^ 2 * ∑ b, Complex.normSq (x (j₀, b)) else 0 :=
          (if_pos hj₀).symm
      _ ≤ ∑ j, if P i j then c ^ 2 * ∑ b, Complex.normSq (x (j, b)) else 0 :=
          Finset.single_le_sum
            (f := fun j => if P i j then c ^ 2 * ∑ b, Complex.normSq (x (j, b)) else 0)
            (fun j _ => hnn j) (Finset.mem_univ j₀)
  · have hzero : ∀ a, (blockMat A *ᵥ x) (i, a) = 0 := by
      intro a
      rw [blockMat_mulVec_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hz : A i j = 0 := by
        by_contra hne
        exact h ⟨j, hP i j hne⟩
      rw [hz, Matrix.zero_mulVec, Pi.zero_apply]
    have hl : ∑ a, Complex.normSq ((blockMat A *ᵥ x) (i, a)) = 0 :=
      Finset.sum_eq_zero fun a _ => by rw [hzero a, Complex.normSq_zero]
    rw [hl]
    exact Finset.sum_nonneg fun j _ => ite_nonneg (mul_nonneg (sq_nonneg c)
      (Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)) le_rfl

/-- **Norm of a block matrix with partial-permutation support.** If every block has norm at
most `c`, and the nonzero blocks sit inside a relation `P` with at most one entry in every
row and every column, then the whole matrix has norm at most `c`. -/
theorem norm_blockMat_le {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (A : I → I → Matrix W W ℂ) (P : I → I → Prop) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ i j, ‖A i j‖ ≤ c) (hP : ∀ i j, A i j ≠ 0 → P i j)
    (hrow : ∀ i j j', P i j → P i j' → j = j') (hcol : ∀ i i' j, P i j → P i' j → i = i') :
    ‖blockMat A‖ ≤ c := by
  classical
  refine KazhdanCornerMatrices.l2_opNorm_le_of_sum_normSq_general (blockMat A) hc fun x => ?_
  have hN : ∀ j, 0 ≤ c ^ 2 * ∑ b, Complex.normSq (x (j, b)) := fun j =>
    mul_nonneg (sq_nonneg c) (Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)
  calc ∑ p : I × W, Complex.normSq ((blockMat A *ᵥ x) p)
      = ∑ i, ∑ a, Complex.normSq ((blockMat A *ᵥ x) (i, a)) := Fintype.sum_prod_type _
    _ ≤ ∑ i, ∑ j, if P i j then c ^ 2 * ∑ b, Complex.normSq (x (j, b)) else 0 :=
        Finset.sum_le_sum fun i _ => sum_normSq_blockMat_mulVec_row_le A P hA hP hrow x i
    _ = ∑ j, ∑ i, if P i j then c ^ 2 * ∑ b, Complex.normSq (x (j, b)) else 0 :=
        Finset.sum_comm
    _ ≤ ∑ j, c ^ 2 * ∑ b, Complex.normSq (x (j, b)) :=
        Finset.sum_le_sum fun j _ =>
          sum_ite_le_of_subsingleton (fun i => P i j) (hN j) fun i i' hi hi' =>
            hcol i i' j hi hi'
    _ = c ^ 2 * ∑ p : I × W, Complex.normSq (x p) := by
        rw [Fintype.sum_prod_type, Finset.mul_sum]

end GroupApproximation.Full.TWWCyclic
