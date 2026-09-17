import GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.Weights
import GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.Amplification
import GroupApproximation.Manuscript.NonMF.TWWLanes.CommutativeAverage.Rational
import GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.Presentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Rational amplification of tracial states on multimatrix algebras (lane nm-tww-03, part 4)

This module proves the upstream interface `AFQD.MultimatrixTraceAmplificationStatement`,
which is the second clause of the lane. For every tracial state `τ` on `⊕_{i<r} M_{k_i}(ℂ)`
and every `ε > 0` there is a unital ⋆-homomorphism `π : B → M_N(ℂ)` with
`‖τ b − trace (π b) / N‖ ≤ ε ‖b‖`.

## Route

* `exists_weights` gives `τ b = ∑ t i · trace (b i) / k i`, with `t ≥ 0`, `∑ t = 1`, and
  `t i = 0` whenever `k i = 0`.
* Pick an integer `K > r (r + 1) / ε`. Put `c = floorWeights (K + r) t` and `N' = ∑ c`.
  Then `N' ≥ K > 0` and `|N' t i − c i| ≤ r + 1` (`CommutativeAverage.floorWeights_bounds`).
  If `k i = 0` then `c i = 0`.
* Let `L = ∏ max (k j) 1` and `m i = c i · (L / k i)`, so `k i · m i = c i · L`.
  The amplified representation `ampRep m` has size `N = N' L`, and
  `trace (π b) / N = N'⁻¹ ∑ c i · trace (b i) / k i`.
* `|trace (b i) / k i| ≤ ‖b i‖ ≤ ‖b‖`, and `CommutativeAverage.norm_weighted_sub_average_le`
  bounds the error by `N'⁻¹ · r (r + 1) ‖b‖ ≤ ε ‖b‖`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace MultimatrixTrace

open scoped Matrix.Norms.L2Operator

noncomputable section

attribute [local instance] AFQD.matrixBlockCStarAlgebra AFQD.multimatrixCStarAlgebra

/-- **Clause 2 of lane `nm-tww-03`.** A tracial state on a multimatrix algebra is
uniformly approximated, relative to the C⋆-norm, by the normalized trace of a unital
⋆-representation on `ℂ^N`. -/
theorem multimatrixTraceAmplificationStatement : AFQD.MultimatrixTraceAmplificationStatement := by
  intro r k τ ε hε
  obtain ⟨t, ht0, ht1, htk, hτ⟩ := exists_weights r k τ
  obtain ⟨K, hK⟩ := exists_nat_gt (max ((r : ℝ) * ((r : ℝ) + 1) / ε) 0)
  have hM : (0 : ℝ) ≤ (K : ℝ) + r := by positivity
  obtain ⟨hNlow, hcount⟩ := CommutativeAverage.floorWeights_bounds t ht0 ht1 hM
  obtain ⟨c, hc⟩ : ∃ c : Fin r → ℕ, CommutativeAverage.floorWeights ((K : ℝ) + r) t = c :=
    ⟨_, rfl⟩
  rw [hc] at hNlow hcount
  have hc0 : ∀ i, k i = 0 → c i = 0 := by
    intro i hi
    rw [← hc]
    change ⌊((K : ℝ) + r) * t i⌋₊ = 0
    rw [htk i hi, mul_zero, Nat.floor_zero]
  have hKpos : (0 : ℝ) < K := lt_of_le_of_lt (le_max_right _ _) hK
  have hCK : (r : ℝ) * ((r : ℝ) + 1) / ε < K := lt_of_le_of_lt (le_max_left _ _) hK
  have hNreal : (K : ℝ) ≤ ((∑ i, c i : ℕ) : ℝ) := by linarith [hNlow]
  have hNpos : 0 < ∑ i, c i := Nat.cast_pos.1 (lt_of_lt_of_le hKpos hNreal)
  obtain ⟨L, hLpos, hLdvd⟩ : ∃ L : ℕ, 0 < L ∧ ∀ i, k i ≠ 0 → k i ∣ L := by
    refine ⟨∏ j, max (k j) 1,
      Finset.prod_pos fun j _ ↦ lt_of_lt_of_le Nat.one_pos (le_max_right _ _), fun i hk ↦ ?_⟩
    have h1 : k i = max (k i) 1 := (max_eq_left (Nat.one_le_iff_ne_zero.mpr hk)).symm
    have h2 : max (k i) 1 ∣ ∏ j, max (k j) 1 :=
      Finset.dvd_prod_of_mem (fun j ↦ max (k j) 1) (Finset.mem_univ i)
    rw [h1]
    exact h2
  obtain ⟨m, hkm, hm0⟩ : ∃ m : Fin r → ℕ, (∀ i, k i * m i = c i * L) ∧
      ∀ i, k i = 0 → m i = 0 := by
    refine ⟨fun i ↦ c i * (L / k i), fun i ↦ ?_, fun i hk ↦ ?_⟩
    · change k i * (c i * (L / k i)) = c i * L
      by_cases hk : k i = 0
      · rw [hk, hc0 i hk, zero_mul, zero_mul]
      · rw [Nat.mul_left_comm, Nat.mul_div_cancel' (hLdvd i hk)]
    · change c i * (L / k i) = 0
      rw [hk, Nat.div_zero, mul_zero]
  have hcard : Fintype.card (AmpIndex k m) = (∑ i, c i) * L := by
    rw [card_ampIndex, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ ↦ hkm i
  have hL0 : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hLpos.ne'
  refine ⟨Fintype.card (AmpIndex k m), ampRep m, fun b ↦ ?_⟩
  have hterm : ∀ i, (m i : ℂ) * Matrix.trace (b i) =
      (L : ℂ) * ((c i : ℂ) * (Matrix.trace (b i) / (k i : ℂ))) := by
    intro i
    by_cases hk : k i = 0
    · rw [hm0 i hk, hc0 i hk, Nat.cast_zero, zero_mul, zero_mul, mul_zero]
    · have hk0 : (k i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
      have hkmC : (k i : ℂ) * (m i : ℂ) = (c i : ℂ) * (L : ℂ) := by exact_mod_cast hkm i
      calc (m i : ℂ) * Matrix.trace (b i)
          = ((k i : ℂ) * (m i : ℂ)) * (Matrix.trace (b i) / (k i : ℂ)) := by
            rw [mul_comm (k i : ℂ), mul_assoc, mul_div_cancel₀ _ hk0]
        _ = (L : ℂ) * ((c i : ℂ) * (Matrix.trace (b i) / (k i : ℂ))) := by
            rw [hkmC, mul_comm (c i : ℂ) (L : ℂ), mul_assoc]
  have hsum : ∑ i, (m i : ℂ) * Matrix.trace (b i) =
      ∑ i, (L : ℂ) * ((c i : ℂ) * (Matrix.trace (b i) / (k i : ℂ))) :=
    Finset.sum_congr rfl fun i _ ↦ hterm i
  have htr : Matrix.trace (ampRep m b) / ((Fintype.card (AmpIndex k m) : ℕ) : ℂ) =
      ((∑ i, c i : ℕ) : ℂ)⁻¹ * ∑ i, (c i : ℂ) * (Matrix.trace (b i) / (k i : ℂ)) := by
    rw [trace_ampRep, hcard, hsum, ← Finset.mul_sum, Nat.cast_mul,
      mul_comm ((∑ i, c i : ℕ) : ℂ) (L : ℂ), mul_div_mul_left _ _ hL0, div_eq_inv_mul]
  have ha : ∀ i, ‖(fun i ↦ Matrix.trace (b i) / (k i : ℂ)) i‖ ≤ ‖b‖ :=
    fun i ↦ (norm_trace_div_le (k i) (b i)).trans (norm_le_pi_norm b i)
  have hfinal : ((∑ i, c i : ℕ) : ℝ)⁻¹ * ((r : ℝ) * (((r : ℝ) + 1) * ‖b‖)) ≤ ε * ‖b‖ := by
    rw [inv_mul_le_iff₀ (Nat.cast_pos.2 hNpos)]
    have h1 : (r : ℝ) * ((r : ℝ) + 1) < K * ε := (div_lt_iff₀ hε).1 hCK
    have h2 : (K : ℝ) * ε ≤ ((∑ i, c i : ℕ) : ℝ) * ε := mul_le_mul_of_nonneg_right hNreal hε.le
    calc (r : ℝ) * (((r : ℝ) + 1) * ‖b‖) = ((r : ℝ) * ((r : ℝ) + 1)) * ‖b‖ := by ring
      _ ≤ (((∑ i, c i : ℕ) : ℝ) * ε) * ‖b‖ :=
          mul_le_mul_of_nonneg_right (by linarith [h1, h2]) (norm_nonneg b)
      _ = ((∑ i, c i : ℕ) : ℝ) * (ε * ‖b‖) := by ring
  change ‖τ b - Matrix.trace (ampRep m b) / ((Fintype.card (AmpIndex k m) : ℕ) : ℂ)‖ ≤
    ε * ‖b‖
  rw [hτ b, htr]
  exact le_trans (CommutativeAverage.norm_weighted_sub_average_le hNpos t c
    (fun i ↦ Matrix.trace (b i) / (k i : ℂ)) hcount ha (by positivity)) hfinal

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.MultimatrixTrace.multimatrixTraceAmplificationStatement

end

end MultimatrixTrace
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
