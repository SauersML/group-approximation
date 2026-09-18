import GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.RoundingTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# Lane nm-tww-23, endpoint: layer rounding holds

This file proves `LayerRoundingStatement` (ConnesTrick/Endpoint.lean) with no extra hypotheses.
Through `connesTrickStatement_of_layerRounding` it then gives
`NuclearAmenable.ConnesTrickStatement`.

**Constants.** Put `K = 1 + ∑_{x ∈ F} ‖x‖`, `η = ε² / (16 K⁴)`, `t = η⁻¹` and
`A = 1 + K² (1 + t)`. Then `ε₁ = min (ε/2) (ε² / (16 A))`, which depends only on `F` and `ε`.
Given `Y`, take `N = ⌈16 K⁴ #Y / ε² + 4 K #Y / ε + 2 #Y + 1⌉₊` and `c = roundLayers N μ`.

**Multiplicativity.** `sum_normSq_round_defect_le` bounds the unnormalised mass by
`2Nε₁ A + 2K⁴Nη + 2K⁴#Y`, and each of the three terms is at most `Nε²/8`. Since
`S ≥ N - #Y ≥ N/2`, this is at most `ε² S`, and `hsNorm_layerModel_le` gives `hsNorm ≤ ε`.
The case `S = 0` cannot occur, because `S ≥ N - #Y ≥ #Y + 1`.

**Trace.** `norm_sub_normTrace_layer_le` bounds the trace defect by
`ε₁ + K · 2#Y/N ≤ ε/2 + ε/2`.

Everything here is proved.
-/

namespace GroupApproximation
namespace Manuscript.NonMF.TWWLanes.ConnesTrick

open Matrix Quasidiagonal Finset
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

/-- **Layer rounding holds.** -/
theorem layerRoundingStatement_holds : LayerRoundingStatement.{u} := by
  intro A _ τ F ε hε
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + ∑ x ∈ F, ‖x‖ := ⟨_, rfl⟩
  have hsum0 : 0 ≤ ∑ x ∈ F, ‖x‖ := Finset.sum_nonneg fun x _ ↦ norm_nonneg x
  have hKpos : 0 < K := by linarith
  have hFK : ∀ x ∈ F, ‖x‖ ≤ K := fun x hx ↦ by
    have h : ‖x‖ ≤ ∑ y ∈ F, ‖y‖ := Finset.single_le_sum (fun y _ ↦ norm_nonneg y) hx
    linarith
  have h16K : (0 : ℝ) < 16 * K ^ 4 := mul_pos (by norm_num) (pow_pos hKpos 4)
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε ^ 2 / (16 * K ^ 4) := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hηdef]
    exact div_pos (pow_pos hε 2) h16K
  have hη16 : η * (16 * K ^ 4) = ε ^ 2 := by
    rw [hηdef]
    exact div_mul_cancel₀ _ h16K.ne'
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = η⁻¹ := ⟨_, rfl⟩
  have htη : t * η = 1 := by
    rw [htdef]
    exact inv_mul_cancel₀ hηpos.ne'
  have htpos : 0 < t := by
    rw [htdef]
    exact inv_pos.mpr hηpos
  obtain ⟨Aa, hAdef⟩ : ∃ Aa : ℝ, Aa = 1 + K ^ 2 * (1 + t) := ⟨_, rfl⟩
  have hApos : (0 : ℝ) < 16 * Aa := by
    have h : 0 ≤ K ^ 2 * (1 + t) := mul_nonneg (sq_nonneg K) (by linarith)
    linarith
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (ε / 2) (ε ^ 2 / (16 * Aa)) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]
    exact lt_min (half_pos hε) (div_pos (pow_pos hε 2) hApos)
  have hε₁half : ε₁ ≤ ε / 2 := by
    rw [hε₁def]
    exact min_le_left _ _
  have hε₁A : ε₁ * (16 * Aa) ≤ ε ^ 2 := by
    have h : ε₁ ≤ ε ^ 2 / (16 * Aa) := by
      rw [hε₁def]
      exact min_le_right _ _
    exact (le_div_iff₀ hApos).mp h
  refine ⟨ε₁, hε₁pos, ?_⟩
  intro Y B μ hB hμ htr hcomm hmul
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈16 * K ^ 4 * (Fintype.card Y : ℝ) / ε ^ 2
      + 4 * K * (Fintype.card Y : ℝ) / ε + 2 * (Fintype.card Y : ℝ) + 1⌉₊ := ⟨_, rfl⟩
  have hNge : 16 * K ^ 4 * (Fintype.card Y : ℝ) / ε ^ 2
      + 4 * K * (Fintype.card Y : ℝ) / ε + 2 * (Fintype.card Y : ℝ) + 1 ≤ (N : ℝ) := by
    rw [hNdef]
    exact Nat.le_ceil _
  have hcard0 : (0 : ℝ) ≤ (Fintype.card Y : ℝ) := Nat.cast_nonneg _
  have hq1 : 0 ≤ 16 * K ^ 4 * (Fintype.card Y : ℝ) / ε ^ 2 :=
    div_nonneg (mul_nonneg h16K.le hcard0) (sq_nonneg ε)
  have hq2 : 0 ≤ 4 * K * (Fintype.card Y : ℝ) / ε :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hKpos.le) hcard0) hε.le
  have hN2 : 2 * (Fintype.card Y : ℝ) + 1 ≤ (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hNε2 : 16 * K ^ 4 * (Fintype.card Y : ℝ) ≤ (N : ℝ) * ε ^ 2 :=
    (div_le_iff₀ (pow_pos hε 2)).mp (by linarith)
  have hNε : 4 * K * (Fintype.card Y : ℝ) ≤ (N : ℝ) * ε :=
    (div_le_iff₀ hε).mp (by linarith)
  have hSN := sum_roundLayers_le N μ hμ
  have hSc := sub_card_le_sum_roundLayers N μ hμ
  have hS : 0 < ((∑ i, roundLayers N μ i : ℕ) : ℝ) := by linarith
  have hBK : ∀ x ∈ F, ‖B x‖ ≤ K := fun x hx ↦ (hB x).trans (hFK x hx)
  refine ⟨roundLayers N μ, ?_, ?_⟩
  · intro x hx y hy
    have hdef := sum_normSq_round_defect_le N μ hμ (B (x * y)) (B x) (B y) K t η ε₁ htpos
      hηpos.le htη (hBK x hx) (hBK y hy) (hmul x hx y hy) (hcomm y hy)
    refine hsNorm_layerModel_le (roundLayers N μ) _ ε hε.le hS (hdef.trans ?_)
    have h1 := mul_le_mul_of_nonneg_left hε₁A hNpos.le
    rw [hAdef] at h1
    have h2 : (N : ℝ) * (η * (16 * K ^ 4)) = (N : ℝ) * ε ^ 2 := by rw [hη16]
    have h3 := mul_le_mul_of_nonneg_left hSc (sq_nonneg ε)
    have h4 := mul_le_mul_of_nonneg_left hN2 (sq_nonneg ε)
    have h5 : 0 ≤ (N : ℝ) * ε ^ 2 := mul_nonneg hNpos.le (sq_nonneg ε)
    have h6 := sq_nonneg ε
    linarith
  · intro x hx
    have htrace := norm_sub_normTrace_layer_le N μ hμ (roundLayers N μ) (roundLayers_le N μ)
      hSN hSc hS (B x) K hKpos.le (hBK x hx) (τ x) ε₁ (htr x hx)
    refine htrace.trans ?_
    have hq : (Fintype.card Y : ℝ) / (N : ℝ) * (N : ℝ) = (Fintype.card Y : ℝ) :=
      div_mul_cancel₀ _ hNpos.ne'
    have h7 : (N : ℝ) * (K * (2 * ((Fintype.card Y : ℝ) / (N : ℝ)))) ≤ (N : ℝ) * (ε / 2) := by
      calc (N : ℝ) * (K * (2 * ((Fintype.card Y : ℝ) / (N : ℝ))))
          = 2 * K * ((Fintype.card Y : ℝ) / (N : ℝ) * (N : ℝ)) := by ring
        _ = 2 * K * (Fintype.card Y : ℝ) := by rw [hq]
        _ ≤ (N : ℝ) * (ε / 2) := by linarith
    have h8 := le_of_mul_le_mul_left h7 hNpos
    linarith

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.layerRoundingStatement_holds

/-- **Connes' trick** (`NuclearAmenable.ConnesTrickStatement`) holds. -/
theorem connesTrickStatement_holds : NuclearAmenable.ConnesTrickStatement.{u} :=
  connesTrickStatement_of_layerRounding layerRoundingStatement_holds

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.ConnesTrick.connesTrickStatement_holds

end

end Manuscript.NonMF.TWWLanes.ConnesTrick
end GroupApproximation
