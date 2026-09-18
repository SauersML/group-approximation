import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesRoundingRow

/-!
# Connes' trick, layer rounding (part 4): the tail part and the defect estimate

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick),
the rounding of the eigenvalue multiplicities. Adapted, after review, from the never-wired
foreign `TWWLanes/ConnesTrick` rounding module of the same content.

The tail `T_a(i, j) = ∑_{k : cₖ ≤ a} Xᵢₖ Wₖⱼ` only sees rows `k` of `W` with `cₖ ≤ a < cⱼ`.
With `‖X‖ ≤ K`, the tail part of the layered defect is at most
`∑ₖ ∑ⱼ |cⱼ - cₖ| · 2K²|Wₖⱼ|²` (`sum_layer_tail_le`). Together with part 3 this gives
the unnormalised estimate

`∑_{p,q} |(layer c V - layer c X * layer c W) p q|²
  ≤ ∑ᵢ ∑ⱼ cⱼ · 2|(V - X W)ᵢⱼ|² + ∑ₖ ∑ⱼ |cⱼ - cₖ| · 2K²|Wₖⱼ|²`

(`sum_normSq_layer_defect_le`). This is the defect estimate of the proof sketch before the
floor bounds are inserted.

Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : FiniteModel}

/-- The tail part of the layered defect. -/
theorem sum_layer_tail_le (c : Y → ℕ) (X W : Matrix Y Y ℂ) (K : ℝ) (hX : ‖X‖ ≤ K) :
    ∑ i, ∑ a ∈ range (c i), ∑ j,
        (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0)
      ≤ ∑ k, ∑ j, |(c j : ℝ) - (c k : ℝ)| * (2 * K ^ 2 * Complex.normSq (W k j)) := by
  have hT0 : ∀ (a : ℕ) (i j : Y),
      0 ≤ (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0) := by
    intro a i j
    by_cases h : a < c j
    · rw [if_pos h]
      exact mul_nonneg zero_le_two (Complex.normSq_nonneg _)
    · exact le_of_eq (if_neg h).symm
  have hw : ∀ k j : Y, 0 ≤ 2 * K ^ 2 * Complex.normSq (W k j) := fun k j ↦
    mul_nonneg (mul_nonneg zero_le_two (sq_nonneg K)) (Complex.normSq_nonneg _)
  have hle : ∀ i, c i ≤ ∑ l, c l := fun i ↦
    Finset.single_le_sum (fun l _ ↦ Nat.zero_le (c l)) (Finset.mem_univ i)
  have hcol : ∀ (a : ℕ) (j : Y),
      ∑ i, (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0)
        ≤ ∑ k, (if c k ≤ a ∧ a < c j then 2 * K ^ 2 * Complex.normSq (W k j) else 0) := by
    intro a j
    by_cases hP : a < c j
    · calc ∑ i, (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0)
          = 2 * ∑ i, Complex.normSq (layerTail c a X W i j) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ if_pos hP
        _ ≤ 2 * (K ^ 2 * ∑ k, (if c k ≤ a then Complex.normSq (W k j) else 0)) :=
            mul_le_mul_of_nonneg_left (sum_normSq_layerTail_le c a X W K hX j) zero_le_two
        _ = ∑ k, (if c k ≤ a ∧ a < c j then 2 * K ^ 2 * Complex.normSq (W k j) else 0) := by
            rw [← mul_assoc, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            by_cases hk : c k ≤ a
            · have hkP : c k ≤ a ∧ a < c j := ⟨hk, hP⟩
              rw [if_pos hk, if_pos hkP]
            · have hkP : ¬ (c k ≤ a ∧ a < c j) := fun h ↦ hk h.1
              rw [if_neg hk, if_neg hkP, mul_zero]
    · have h1 : ∑ i, (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0)
          = 0 := Finset.sum_eq_zero fun i _ ↦ if_neg hP
      have hkP : ∀ k, ¬ (c k ≤ a ∧ a < c j) := fun k h ↦ hP h.2
      have h2 : ∑ k, (if c k ≤ a ∧ a < c j then 2 * K ^ 2 * Complex.normSq (W k j) else 0)
          = 0 := Finset.sum_eq_zero fun k _ ↦ if_neg (hkP k)
      exact le_of_eq (h1.trans h2.symm)
  calc ∑ i, ∑ a ∈ range (c i), ∑ j,
        (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0)
      ≤ ∑ i, ∑ a ∈ range (∑ l, c l), ∑ j,
          (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (hle i))
          (fun a _ _ ↦ Finset.sum_nonneg fun j _ ↦ hT0 a i j)
    _ = ∑ a ∈ range (∑ l, c l), ∑ i, ∑ j,
          (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0) :=
        Finset.sum_comm
    _ = ∑ a ∈ range (∑ l, c l), ∑ j, ∑ i,
          (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ ≤ ∑ a ∈ range (∑ l, c l), ∑ j, ∑ k,
          (if c k ≤ a ∧ a < c j then 2 * K ^ 2 * Complex.normSq (W k j) else 0) :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun j _ ↦ hcol a j
    _ = ∑ j, ∑ a ∈ range (∑ l, c l), ∑ k,
          (if c k ≤ a ∧ a < c j then 2 * K ^ 2 * Complex.normSq (W k j) else 0) :=
        Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ a ∈ range (∑ l, c l),
          (if c k ≤ a ∧ a < c j then 2 * K ^ 2 * Complex.normSq (W k j) else 0) :=
        Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ a ∈ range (∑ l, c l),
          (if c k ≤ a ∧ a < c j then 2 * K ^ 2 * Complex.normSq (W k j) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ k, ∑ j, |(c j : ℝ) - (c k : ℝ)| * (2 * K ^ 2 * Complex.normSq (W k j)) :=
        Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun j _ ↦
          sum_range_ite_Ico_le (∑ l, c l) (c k) (c j) _ (hw k j)

/-- The unnormalised defect estimate for the layered model. -/
theorem sum_normSq_layer_defect_le (c : Y → ℕ) (V X W : Matrix Y Y ℂ) (K : ℝ)
    (hX : ‖X‖ ≤ K) :
    ∑ p : layerModel Y c, ∑ q : layerModel Y c,
        Complex.normSq ((layer c V - layer c X * layer c W) p q)
      ≤ ∑ i, ∑ j, (c j : ℝ) * (2 * Complex.normSq ((V - X * W) i j))
        + ∑ k, ∑ j, |(c j : ℝ) - (c k : ℝ)| * (2 * K ^ 2 * Complex.normSq (W k j)) := by
  calc ∑ p : layerModel Y c, ∑ q : layerModel Y c,
        Complex.normSq ((layer c V - layer c X * layer c W) p q)
      = ∑ i, ∑ a ∈ range (c i), ∑ j, (if a < c j then
          Complex.normSq ((V - X * W) i j + layerTail c a X W i j) else 0) :=
        sum_normSq_layer_defect_eq c V X W
    _ ≤ ∑ i, ∑ a ∈ range (c i), ∑ j,
          (if a < c j then 2 * Complex.normSq ((V - X * W) i j) else 0)
        + ∑ i, ∑ a ∈ range (c i), ∑ j,
            (if a < c j then 2 * Complex.normSq (layerTail c a X W i j) else 0) :=
        sum_normSq_layer_defect_split c (fun _ i j ↦ (V - X * W) i j)
          (fun a i j ↦ layerTail c a X W i j)
    _ ≤ ∑ i, ∑ j, (c j : ℝ) * (2 * Complex.normSq ((V - X * W) i j))
        + ∑ k, ∑ j, |(c j : ℝ) - (c k : ℝ)| * (2 * K ^ 2 * Complex.normSq (W k j)) :=
        add_le_add
          (sum_layer_count_le c (fun i j ↦ 2 * Complex.normSq ((V - X * W) i j))
            (fun _ _ ↦ mul_nonneg zero_le_two (Complex.normSq_nonneg _)))
          (sum_layer_tail_le c X W K hX)

end

end GroupApproximation.Full.TWWSchafhauser.Connes
