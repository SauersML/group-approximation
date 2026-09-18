import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesRoundingDefect

/-!
# Connes' trick, layer rounding (part 7): the entry bound and the trace estimate

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick),
the rounding of the eigenvalue multiplicities. Adapted, after review, from the never-wired
foreign `TWWLanes/ConnesTrick` rounding module of the same content.

* Contractivity bounds the entries: `‖M‖ ≤ K` gives `|Mᵢⱼ| ≤ K`
  (`norm_entry_le_of_opNorm_le`).
* The normalised trace of a layered matrix is `∑ᵢ (cᵢ / S) Mᵢᵢ` with `S = ∑ᵢ cᵢ`
  (`normTrace_layer_eq_sum`).
* Suppose `cᵢ ≤ N μᵢ²`, `N - #Y ≤ S ≤ N`, `0 < S` and `∑ᵢ μᵢ² = 1`. Then
  `∑ᵢ |μᵢ² - cᵢ/S| ≤ 2 (1 - S/N) ≤ 2 #Y / N`, so the trace defect is at most
  `ε₁ + K · 2 #Y / N` (`norm_sub_normTrace_layer_le`).

Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : FiniteModel}

/-- The entries of a matrix are bounded by its operator norm. -/
theorem norm_entry_le_of_opNorm_le (M : Matrix Y Y ℂ) (K : ℝ) (hK : 0 ≤ K) (hM : ‖M‖ ≤ K)
    (i j : Y) : ‖M i j‖ ≤ K := by
  have h1 := normSq_entry_le_sq_l2_opNorm Y M i j
  rw [Complex.normSq_eq_norm_sq] at h1
  exact le_of_pow_le_pow_left₀ two_ne_zero hK
    (h1.trans (pow_le_pow_left₀ (norm_nonneg _) hM 2))

/-- The normalised trace of a layered matrix as a weighted diagonal sum. -/
theorem normTrace_layer_eq_sum (c : Y → ℕ) (M : Matrix Y Y ℂ) :
    normTrace (layerModel Y c) (layer c M)
      = ∑ i, (((c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) : ℝ) : ℂ) * M i i := by
  rw [normTrace_layer, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]
  ring

/-- The trace estimate for layered multiplicities with total between `N - #Y` and `N`. -/
theorem norm_sub_normTrace_layer_le (N : ℕ) (μ : Y → ℝ) (hμ : ∑ i, μ i ^ 2 = 1)
    (c : Y → ℕ) (hc : ∀ i, (c i : ℝ) ≤ (N : ℝ) * μ i ^ 2)
    (hSN : ((∑ l, c l : ℕ) : ℝ) ≤ (N : ℝ))
    (hSc : (N : ℝ) - (Fintype.card Y : ℝ) ≤ ((∑ l, c l : ℕ) : ℝ))
    (hS : 0 < ((∑ l, c l : ℕ) : ℝ))
    (M : Matrix Y Y ℂ) (K : ℝ) (hK : 0 ≤ K) (hM : ‖M‖ ≤ K) (z : ℂ) (ε₁ : ℝ)
    (hz : ‖z - ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * M i i‖ ≤ ε₁) :
    ‖z - normTrace (layerModel Y c) (layer c M)‖
      ≤ ε₁ + K * (2 * ((Fintype.card Y : ℝ) / (N : ℝ))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hS hSN
  rw [normTrace_layer_eq_sum]
  have hdiff : ∑ i, (((μ i ^ 2 - (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ)) : ℝ) : ℂ) * M i i
      = ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * M i i
        - ∑ i, (((c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) : ℝ) : ℂ) * M i i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Complex.ofReal_sub, sub_mul]
  have hsplit : z - ∑ i, (((c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) : ℝ) : ℂ) * M i i
      = (z - ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * M i i)
        + ∑ i, (((μ i ^ 2 - (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ)) : ℝ) : ℂ) * M i i := by
    rw [hdiff]
    ring
  have hpt : ∀ i, |μ i ^ 2 - (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ)|
      ≤ (μ i ^ 2 - (c i : ℝ) / (N : ℝ))
        + ((c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) - (c i : ℝ) / (N : ℝ)) := by
    intro i
    have h1 : (c i : ℝ) / (N : ℝ) ≤ μ i ^ 2 := by
      rw [div_le_iff₀ hNpos]
      have := hc i
      linarith
    have h2 : (c i : ℝ) / (N : ℝ) ≤ (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) hS hSN
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hnorm : ‖∑ i, (((μ i ^ 2 - (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ)) : ℝ) : ℂ) * M i i‖
      ≤ ∑ i, |μ i ^ 2 - (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ)| * K := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_entry_le_of_opNorm_le M K hK hM i i) (abs_nonneg _)
  have hsum : ∑ i, |μ i ^ 2 - (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ)| * K
      ≤ ∑ i, ((μ i ^ 2 - (c i : ℝ) / (N : ℝ))
        + ((c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) - (c i : ℝ) / (N : ℝ))) * K :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hpt i) hK
  have hA : ∑ i, (c i : ℝ) / (N : ℝ) = ((∑ l, c l : ℕ) : ℝ) / (N : ℝ) := by
    rw [← Finset.sum_div, Nat.cast_sum]
  have hB : ∑ i, (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, div_self hS.ne']
  have hval : ∑ i, ((μ i ^ 2 - (c i : ℝ) / (N : ℝ))
        + ((c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) - (c i : ℝ) / (N : ℝ))) * K
      = ((1 - ((∑ l, c l : ℕ) : ℝ) / (N : ℝ)) + (1 - ((∑ l, c l : ℕ) : ℝ) / (N : ℝ))) * K := by
    rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, hμ, hA, hB]
  have hD : ((N : ℝ) - (Fintype.card Y : ℝ)) / (N : ℝ) ≤ ((∑ l, c l : ℕ) : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right hSc hNpos.le
  have hE : ((N : ℝ) - (Fintype.card Y : ℝ)) / (N : ℝ)
      = 1 - (Fintype.card Y : ℝ) / (N : ℝ) := by
    rw [sub_div, div_self hNpos.ne']
  have h5 : 1 - ((∑ l, c l : ℕ) : ℝ) / (N : ℝ) ≤ (Fintype.card Y : ℝ) / (N : ℝ) := by
    linarith
  have h6 := mul_le_mul_of_nonneg_left h5 hK
  calc ‖z - ∑ i, (((c i : ℝ) / ((∑ l, c l : ℕ) : ℝ) : ℝ) : ℂ) * M i i‖
      = ‖(z - ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * M i i)
        + ∑ i, (((μ i ^ 2 - (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ)) : ℝ) : ℂ) * M i i‖ := by
        rw [hsplit]
    _ ≤ ‖z - ∑ i, ((μ i ^ 2 : ℝ) : ℂ) * M i i‖
        + ‖∑ i, (((μ i ^ 2 - (c i : ℝ) / ((∑ l, c l : ℕ) : ℝ)) : ℝ) : ℂ) * M i i‖ :=
        norm_add_le _ _
    _ ≤ ε₁ + K * (2 * ((Fintype.card Y : ℝ) / (N : ℝ))) := by
        have h7 := hnorm.trans (hsum.trans (le_of_eq hval))
        linarith

end

end GroupApproximation.Full.TWWSchafhauser.Connes
