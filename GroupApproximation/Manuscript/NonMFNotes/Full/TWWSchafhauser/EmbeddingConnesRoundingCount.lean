import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesRoundingLayer

/-!
# Connes' trick, layer rounding (part 2): counting and entry estimates for the rounding step

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick),
the rounding of the eigenvalue multiplicities. Adapted, after review, from the never-wired
foreign `TWWLanes/ConnesTrick` rounding module of the same content.

Small estimates that the Hilbert–Schmidt bound for the layered defect uses.

* `normSq (u + v) ≤ 2 normSq u + 2 normSq v` (`normSq_add_le_two`).
* Layer counts: `∑_{a < m} [a < n] v ≤ n v` (`sum_range_ite_lt_le`) and
  `∑_{a < L} [m ≤ a < n] v ≤ |n - m| v` (`sum_range_ite_Ico_le`).
* Column bound from contractivity: `∑ᵢ |Cᵢⱼ|² ≤ ‖C‖²` (`sum_normSq_col_le`).
* The tail entries `layerTail c a X W i j = (X *ᵥ E_a W e_j)ᵢ` give
  `∑ᵢ |layerTail|² ≤ K² ∑_{k : cₖ ≤ a} |Wₖⱼ|²` whenever `‖X‖ ≤ K`
  (`sum_normSq_layerTail_le`).

Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : FiniteModel}

/-- The parallelogram estimate `|u + v|² ≤ 2|u|² + 2|v|²`. -/
theorem normSq_add_le_two (u v : ℂ) :
    Complex.normSq (u + v) ≤ 2 * Complex.normSq u + 2 * Complex.normSq v := by
  have h1 := Complex.normSq_add u v
  have h2 := Complex.normSq_sub u v
  have h3 := Complex.normSq_nonneg (u - v)
  linarith

/-- The number of layers `a < m` below `n` is at most `n`. -/
theorem sum_range_ite_lt_le (m n : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    ∑ a ∈ range m, (if a < n then v else 0) ≤ (n : ℝ) * v := by
  have hsub : (range m).filter (fun a ↦ a < n) ⊆ range n := fun a ha ↦
    Finset.mem_range.mpr (Finset.mem_filter.mp ha).2
  have hcard : ((((range m).filter (fun a ↦ a < n)).card : ℕ) : ℝ) ≤ (n : ℝ) := by
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    exact_mod_cast h
  calc ∑ a ∈ range m, (if a < n then v else 0)
      = ∑ a ∈ (range m).filter (fun a ↦ a < n), v := (Finset.sum_filter _ _).symm
    _ = ((((range m).filter (fun a ↦ a < n)).card : ℕ) : ℝ) * v := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) * v := mul_le_mul_of_nonneg_right hcard hv

/-- Truncated subtraction is at most the distance of the casts. -/
theorem natSub_cast_le_abs (n m : ℕ) : ((n - m : ℕ) : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by
  rcases le_total m n with h | h
  · rw [Nat.cast_sub h]
    exact le_abs_self _
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    exact abs_nonneg _

/-- The number of layers `a` with `m ≤ a < n` is at most `|n - m|`. -/
theorem sum_range_ite_Ico_le (L m n : ℕ) (v : ℝ) (hv : 0 ≤ v) :
    ∑ a ∈ range L, (if m ≤ a ∧ a < n then v else 0) ≤ |(n : ℝ) - (m : ℝ)| * v := by
  have hsub : (range L).filter (fun a ↦ m ≤ a ∧ a < n) ⊆ Finset.Ico m n := fun a ha ↦
    Finset.mem_Ico.mpr (Finset.mem_filter.mp ha).2
  have hcard : ((((range L).filter (fun a ↦ m ≤ a ∧ a < n)).card : ℕ) : ℝ)
      ≤ |(n : ℝ) - (m : ℝ)| := by
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ico] at h
    have h2 : ((((range L).filter (fun a ↦ m ≤ a ∧ a < n)).card : ℕ) : ℝ)
        ≤ ((n - m : ℕ) : ℝ) := by
      exact_mod_cast h
    exact h2.trans (natSub_cast_le_abs n m)
  calc ∑ a ∈ range L, (if m ≤ a ∧ a < n then v else 0)
      = ∑ a ∈ (range L).filter (fun a ↦ m ≤ a ∧ a < n), v := (Finset.sum_filter _ _).symm
    _ = ((((range L).filter (fun a ↦ m ≤ a ∧ a < n)).card : ℕ) : ℝ) * v := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ |(n : ℝ) - (m : ℝ)| * v := mul_le_mul_of_nonneg_right hcard hv

/-- Every column of a matrix has Hilbert–Schmidt mass at most the squared operator norm. -/
theorem sum_normSq_col_le (C : Matrix Y Y ℂ) (j : Y) :
    ∑ i, Complex.normSq (C i j) ≤ ‖C‖ ^ 2 := by
  classical
  have h := sum_normSq_mulVec_le Y C (Pi.single j 1)
  have hx : ∑ k : Y, Complex.normSq ((Pi.single j (1 : ℂ) : Y → ℂ) k) = 1 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hcolv : ∀ k : Y, (C *ᵥ Pi.single j (1 : ℂ)) k = C k j := by
    intro k
    rw [Matrix.mulVec_single_one]
    rfl
  rw [hx, mul_one] at h
  calc ∑ i : Y, Complex.normSq (C i j)
      = ∑ i : Y, Complex.normSq ((C *ᵥ Pi.single j (1 : ℂ)) i) :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hcolv i]
    _ ≤ ‖C‖ ^ 2 := h

/-- The tail entries on layer `a` are controlled by the operator norm of `X` and the
entries of `W` in the rows `k` with `cₖ ≤ a`. -/
theorem sum_normSq_layerTail_le (c : Y → ℕ) (a : ℕ) (X W : Matrix Y Y ℂ) (K : ℝ)
    (hX : ‖X‖ ≤ K) (j : Y) :
    ∑ i, Complex.normSq (layerTail c a X W i j)
      ≤ K ^ 2 * ∑ k, (if c k ≤ a then Complex.normSq (W k j) else 0) := by
  have hv : ∀ i, (X *ᵥ fun k ↦ if c k ≤ a then W k j else 0) i = layerTail c a X W i j := by
    intro i
    show ∑ k, X i k * (if c k ≤ a then W k j else 0)
      = ∑ k, if c k ≤ a then X i k * W k j else 0
    exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_ite, mul_zero]
  have h1 := sum_normSq_mulVec_le Y X (fun k ↦ if c k ≤ a then W k j else 0)
  have h2 : ∑ k, Complex.normSq (if c k ≤ a then W k j else 0)
      = ∑ k, (if c k ≤ a then Complex.normSq (W k j) else 0) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : c k ≤ a
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk, Complex.normSq_zero]
  have hK2 : ‖X‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hX 2
  have h0 : 0 ≤ ∑ k, Complex.normSq (if c k ≤ a then W k j else 0) :=
    Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
  calc ∑ i, Complex.normSq (layerTail c a X W i j)
      = ∑ i, Complex.normSq ((X *ᵥ fun k ↦ if c k ≤ a then W k j else 0) i) :=
        Finset.sum_congr rfl fun i _ ↦ by rw [hv i]
    _ ≤ ‖X‖ ^ 2 * ∑ k, Complex.normSq (if c k ≤ a then W k j else 0) := h1
    _ ≤ K ^ 2 * ∑ k, Complex.normSq (if c k ≤ a then W k j else 0) :=
        mul_le_mul_of_nonneg_right hK2 h0
    _ = K ^ 2 * ∑ k, (if c k ≤ a then Complex.normSq (W k j) else 0) := by rw [h2]

end

end GroupApproximation.Full.TWWSchafhauser.Connes
