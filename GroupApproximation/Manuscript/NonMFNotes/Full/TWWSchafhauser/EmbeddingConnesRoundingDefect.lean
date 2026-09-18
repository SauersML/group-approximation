import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.EmbeddingConnesRoundingFloor

/-!
# Connes' trick, layer rounding (part 6): the defect estimate for the floor multiplicities

Lane TWWSch3b1 (WO-TWWSch-3b-1), toward `isAmenableTrace_of_isNuclearCStarAlgebra`
(`non_mf_group_notes.tex`, Tikuisis--White--Winter input to Schafhauser's argument). Source:
Brown--Ozawa, *C⋆-algebras and finite-dimensional approximations*, Thm 6.2.7 (Connes' trick),
the rounding of the eigenvalue multiplicities. Adapted, after review, from the never-wired
foreign `TWWLanes/ConnesTrick` rounding module of the same content.

Take `cᵢ = ⌊N μᵢ²⌋₊`, `∑ᵢ μᵢ² = 1`, `‖X‖, ‖W‖ ≤ K` and `t η = 1`. Suppose the weighted
multiplicative defect `∑ᵢⱼ |(V - X W)ᵢⱼ|² μⱼ²` and the commutator weight
`∑ᵢⱼ |Wᵢⱼ|² (μⱼ - μᵢ)²` are both at most `ε₁`. Then the unnormalised Hilbert–Schmidt
mass of `layer c V - layer c X * layer c W` is at most

`2 N ε₁ + 2K² (N (1 + t) ε₁ + N η K² + #Y K²)`

(`sum_normSq_round_defect_le`). `hsNorm_layerModel_le` converts an unnormalised bound
`≤ ε² S` with `S = ∑ᵢ cᵢ > 0` into `hsNorm ≤ ε`. The normalisation of `hsNorm` is by the
number of points of the layered model, and that number is `S`.

Everything here is proved.
-/

namespace GroupApproximation.Full.TWWSchafhauser.Connes

open Matrix Quasidiagonal Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {Y : FiniteModel}

/-- The unnormalised defect estimate for the floor multiplicities. -/
theorem sum_normSq_round_defect_le (N : ℕ) (μ : Y → ℝ) (hμ : ∑ i, μ i ^ 2 = 1)
    (V X W : Matrix Y Y ℂ) (K t η ε₁ : ℝ) (ht : 0 < t) (hη : 0 ≤ η) (htη : t * η = 1)
    (hX : ‖X‖ ≤ K) (hW : ‖W‖ ≤ K)
    (hmult : ∑ i, ∑ j, Complex.normSq ((V - X * W) i j) * μ j ^ 2 ≤ ε₁)
    (hcomm : ∑ i, ∑ j, Complex.normSq (W i j) * (μ j - μ i) ^ 2 ≤ ε₁) :
    ∑ p : layerModel Y (roundLayers N μ), ∑ q : layerModel Y (roundLayers N μ),
        Complex.normSq ((layer (roundLayers N μ) V
          - layer (roundLayers N μ) X * layer (roundLayers N μ) W) p q)
      ≤ 2 * (N : ℝ) * ε₁ + 2 * K ^ 2 * ((N : ℝ) * (1 + t) * ε₁ + (N : ℝ) * η * K ^ 2
          + (Fintype.card Y : ℝ) * K ^ 2) := by
  have hbase := sum_normSq_layer_defect_le (roundLayers N μ) V X W K hX
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hF : ∑ i, ∑ j, (roundLayers N μ j : ℝ) * (2 * Complex.normSq ((V - X * W) i j))
      ≤ 2 * (N : ℝ) * ε₁ := by
    calc ∑ i, ∑ j, (roundLayers N μ j : ℝ) * (2 * Complex.normSq ((V - X * W) i j))
        ≤ ∑ i, ∑ j, ((N : ℝ) * μ j ^ 2) * (2 * Complex.normSq ((V - X * W) i j)) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
            mul_le_mul_of_nonneg_right (roundLayers_le N μ j)
              (mul_nonneg zero_le_two (Complex.normSq_nonneg _))
      _ = ∑ i, ∑ j, 2 * (N : ℝ) * (Complex.normSq ((V - X * W) i j) * μ j ^ 2) :=
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      _ = 2 * (N : ℝ) * ∑ i, ∑ j, Complex.normSq ((V - X * W) i j) * μ j ^ 2 := by
          simp only [Finset.mul_sum]
      _ ≤ 2 * (N : ℝ) * ε₁ := mul_le_mul_of_nonneg_left hmult (mul_nonneg zero_le_two hN)
  have hK2 : ‖W‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hW 2
  have hcolK : ∀ j, ∑ k, Complex.normSq (W k j) ≤ K ^ 2 := fun j ↦
    (sum_normSq_col_le W j).trans hK2
  have hS2 : ∑ k, ∑ j, Complex.normSq (W k j) * μ j ^ 2 ≤ K ^ 2 := by
    calc ∑ k, ∑ j, Complex.normSq (W k j) * μ j ^ 2
        = ∑ j, ∑ k, Complex.normSq (W k j) * μ j ^ 2 := Finset.sum_comm
      _ = ∑ j, μ j ^ 2 * ∑ k, Complex.normSq (W k j) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
      _ ≤ ∑ j, μ j ^ 2 * K ^ 2 :=
          Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hcolK j) (sq_nonneg _)
      _ = K ^ 2 := by rw [← Finset.sum_mul, hμ, one_mul]
  have hS3 : ∑ k, ∑ j, Complex.normSq (W k j) ≤ (Fintype.card Y : ℝ) * K ^ 2 := by
    calc ∑ k, ∑ j, Complex.normSq (W k j) = ∑ j, ∑ k, Complex.normSq (W k j) :=
          Finset.sum_comm
      _ ≤ ∑ _j : Y, K ^ 2 := Finset.sum_le_sum fun j _ ↦ hcolK j
      _ = (Fintype.card Y : ℝ) * K ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hw : ∀ k j : Y, 0 ≤ 2 * K ^ 2 * Complex.normSq (W k j) := fun k j ↦
    mul_nonneg (mul_nonneg zero_le_two (sq_nonneg K)) (Complex.normSq_nonneg _)
  have ha : 0 ≤ 2 * K ^ 2 * (N : ℝ) * (1 + t) :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg K)) hN) (by linarith)
  have hb : 0 ≤ 2 * K ^ 2 * (N : ℝ) * η :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg K)) hN) hη
  have hc : 0 ≤ 2 * K ^ 2 := mul_nonneg zero_le_two (sq_nonneg K)
  have hG : ∑ k, ∑ j, |(roundLayers N μ j : ℝ) - (roundLayers N μ k : ℝ)|
        * (2 * K ^ 2 * Complex.normSq (W k j))
      ≤ 2 * K ^ 2 * (N : ℝ) * (1 + t) * ε₁ + 2 * K ^ 2 * (N : ℝ) * η * K ^ 2
        + 2 * K ^ 2 * ((Fintype.card Y : ℝ) * K ^ 2) := by
    calc ∑ k, ∑ j, |(roundLayers N μ j : ℝ) - (roundLayers N μ k : ℝ)|
          * (2 * K ^ 2 * Complex.normSq (W k j))
        ≤ ∑ k, ∑ j, ((N : ℝ) * (1 + t) * (μ j - μ k) ^ 2 + (N : ℝ) * η * μ j ^ 2 + 1)
          * (2 * K ^ 2 * Complex.normSq (W k j)) :=
          Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun j _ ↦
            mul_le_mul_of_nonneg_right (abs_roundLayers_sub_le N μ t η ht htη j k) (hw k j)
      _ = ∑ k, ∑ j, (2 * K ^ 2 * (N : ℝ) * (1 + t)
              * (Complex.normSq (W k j) * (μ j - μ k) ^ 2)
            + 2 * K ^ 2 * (N : ℝ) * η * (Complex.normSq (W k j) * μ j ^ 2)
            + 2 * K ^ 2 * Complex.normSq (W k j)) :=
          Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
      _ = 2 * K ^ 2 * (N : ℝ) * (1 + t)
              * ∑ k, ∑ j, Complex.normSq (W k j) * (μ j - μ k) ^ 2
            + 2 * K ^ 2 * (N : ℝ) * η * ∑ k, ∑ j, Complex.normSq (W k j) * μ j ^ 2
            + 2 * K ^ 2 * ∑ k, ∑ j, Complex.normSq (W k j) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * K ^ 2 * (N : ℝ) * (1 + t) * ε₁ + 2 * K ^ 2 * (N : ℝ) * η * K ^ 2
            + 2 * K ^ 2 * ((Fintype.card Y : ℝ) * K ^ 2) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hcomm ha)
            (mul_le_mul_of_nonneg_left hS2 hb)) (mul_le_mul_of_nonneg_left hS3 hc)
  linarith

/-- An unnormalised bound `≤ ε² S` on a layered matrix gives `hsNorm ≤ ε`. -/
theorem hsNorm_layerModel_le (c : Y → ℕ) (D : Matrix (layerModel Y c) (layerModel Y c) ℂ)
    (ε : ℝ) (hε : 0 ≤ ε) (hS : 0 < ((∑ i, c i : ℕ) : ℝ))
    (h : ∑ p : layerModel Y c, ∑ q : layerModel Y c, Complex.normSq (D p q)
      ≤ ε ^ 2 * ((∑ i, c i : ℕ) : ℝ)) :
    hsNorm (layerModel Y c) D ≤ ε := by
  show Real.sqrt (hsNormSq (layerModel Y c) D) ≤ ε
  rw [Real.sqrt_le_left hε]
  show (∑ p : layerModel Y c, ∑ q : layerModel Y c, Complex.normSq (D p q))
      / ((Fintype.card (layerModel Y c) : ℕ) : ℝ) ≤ ε ^ 2
  rw [card_layerModel, div_le_iff₀ hS]
  exact h

end

end GroupApproximation.Full.TWWSchafhauser.Connes
