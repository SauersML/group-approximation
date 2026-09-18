import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesRoundingTail

/-!
# Connes' trick, layer rounding (part 5): the floor multiplicities

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick),
the rounding of the eigenvalue multiplicities. Adapted, after review, from the never-wired
foreign `TWWLanes/ConnesTrick` rounding module of the same content.

The multiplicities are `cᵢ = ⌊N μᵢ²⌋₊` (`roundLayers N μ`). This file proves:

* `N μᵢ² - 1 < cᵢ ≤ N μᵢ²` (`roundLayers_le`, `lt_roundLayers_add_one`);
* for `∑ᵢ μᵢ² = 1` the total `S = ∑ᵢ cᵢ` satisfies `N - #Y ≤ S ≤ N`
  (`sum_roundLayers_le`, `sub_card_le_sum_roundLayers`);
* the weighted AM–GM estimate `|m² - n²| ≤ (1 + t)(m - n)² + η m²` for `t η = 1`
  (`abs_sq_sub_sq_le`);
* hence `|cⱼ - cₖ| ≤ N(1 + t)(μⱼ - μₖ)² + N η μⱼ² + 1` (`abs_roundLayers_sub_le`).

Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal Finset

noncomputable section

variable {Y : FiniteModel}

/-- The floor multiplicities `cᵢ = ⌊N μᵢ²⌋₊`. -/
def roundLayers (N : ℕ) (μ : Y → ℝ) (i : Y) : ℕ :=
  ⌊(N : ℝ) * μ i ^ 2⌋₊

theorem roundLayers_le (N : ℕ) (μ : Y → ℝ) (i : Y) :
    (roundLayers N μ i : ℝ) ≤ (N : ℝ) * μ i ^ 2 :=
  Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg (μ i)))

theorem lt_roundLayers_add_one (N : ℕ) (μ : Y → ℝ) (i : Y) :
    (N : ℝ) * μ i ^ 2 < (roundLayers N μ i : ℝ) + 1 :=
  Nat.lt_floor_add_one _

theorem sum_roundLayers_le (N : ℕ) (μ : Y → ℝ) (hμ : ∑ i, μ i ^ 2 = 1) :
    ((∑ i, roundLayers N μ i : ℕ) : ℝ) ≤ (N : ℝ) := by
  rw [Nat.cast_sum]
  calc ∑ i, (roundLayers N μ i : ℝ) ≤ ∑ i, (N : ℝ) * μ i ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ roundLayers_le N μ i
    _ = (N : ℝ) := by rw [← Finset.mul_sum, hμ, mul_one]

theorem sub_card_le_sum_roundLayers (N : ℕ) (μ : Y → ℝ) (hμ : ∑ i, μ i ^ 2 = 1) :
    (N : ℝ) - (Fintype.card Y : ℝ) ≤ ((∑ i, roundLayers N μ i : ℕ) : ℝ) := by
  rw [Nat.cast_sum]
  have h : ∑ i, (N : ℝ) * μ i ^ 2 ≤ ∑ i, ((roundLayers N μ i : ℝ) + 1) :=
    Finset.sum_le_sum fun i _ ↦ (lt_roundLayers_add_one N μ i).le
  have h1 : ∑ i, (N : ℝ) * μ i ^ 2 = (N : ℝ) := by rw [← Finset.mul_sum, hμ, mul_one]
  have h2 : ∑ i, ((roundLayers N μ i : ℝ) + 1)
      = ∑ i, (roundLayers N μ i : ℝ) + (Fintype.card Y : ℝ) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  linarith

/-- Weighted AM–GM control of a difference of squares. -/
theorem abs_sq_sub_sq_le (m n t η : ℝ) (ht : 0 < t) (htη : t * η = 1) :
    |m ^ 2 - n ^ 2| ≤ (1 + t) * (m - n) ^ 2 + η * m ^ 2 := by
  have hAM : 2 * |m| * |m - n| ≤ t * (m - n) ^ 2 + η * m ^ 2 := by
    have h1 := sq_abs (m - n)
    have h2 := sq_abs m
    have hsq : t * (t * (m - n) ^ 2 + η * m ^ 2 - 2 * |m| * |m - n|)
        = (t * |m - n| - |m|) ^ 2 := by
      linear_combination (-t ^ 2) * h1 + m ^ 2 * htη + (-1 : ℝ) * h2
    have hnn : 0 ≤ t * (t * (m - n) ^ 2 + η * m ^ 2 - 2 * |m| * |m - n|) := by
      rw [hsq]
      exact sq_nonneg _
    have h3 := (mul_nonneg_iff_of_pos_left ht).mp hnn
    linarith
  have hprod := abs_mul m (m - n)
  have hle := le_abs_self (m * (m - n))
  have hge := neg_abs_le (m * (m - n))
  have hd := sq_nonneg (m - n)
  have hsplit : m ^ 2 - n ^ 2 = 2 * (m * (m - n)) - (m - n) ^ 2 := by ring
  have habs : |m ^ 2 - n ^ 2| ≤ 2 * |m| * |m - n| + (m - n) ^ 2 := by
    rw [hsplit]
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith
    · linarith
  linarith

/-- Neighbouring multiplicities differ by the commutator weight, an `η`-fraction of the
mass, and one rounding unit. -/
theorem abs_roundLayers_sub_le (N : ℕ) (μ : Y → ℝ) (t η : ℝ) (ht : 0 < t) (htη : t * η = 1)
    (j k : Y) :
    |(roundLayers N μ j : ℝ) - (roundLayers N μ k : ℝ)|
      ≤ (N : ℝ) * (1 + t) * (μ j - μ k) ^ 2 + (N : ℝ) * η * μ j ^ 2 + 1 := by
  have h1 := roundLayers_le N μ j
  have h2 := roundLayers_le N μ k
  have h3 := lt_roundLayers_add_one N μ j
  have h4 := lt_roundLayers_add_one N μ k
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h5 := abs_sq_sub_sq_le (μ j) (μ k) t η ht htη
  have h6 : μ j ^ 2 - μ k ^ 2 ≤ |μ j ^ 2 - μ k ^ 2| := le_abs_self _
  have h7 : μ k ^ 2 - μ j ^ 2 ≤ |μ j ^ 2 - μ k ^ 2| := by
    have := neg_abs_le (μ j ^ 2 - μ k ^ 2)
    linarith
  have h8 : (N : ℝ) * (μ j ^ 2 - μ k ^ 2)
      ≤ (N : ℝ) * ((1 + t) * (μ j - μ k) ^ 2 + η * μ j ^ 2) :=
    mul_le_mul_of_nonneg_left (h6.trans h5) hN
  have h9 : (N : ℝ) * (μ k ^ 2 - μ j ^ 2)
      ≤ (N : ℝ) * ((1 + t) * (μ j - μ k) ^ 2 + η * μ j ^ 2) :=
    mul_le_mul_of_nonneg_left (h7.trans h5) hN
  refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

end

end GroupApproximation.Full.TWWSchafhauser.Connes
