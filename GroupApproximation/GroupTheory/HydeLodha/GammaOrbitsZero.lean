import GroupApproximation.GroupTheory.HydeLodha.GammaTwo
import GroupApproximation.GroupTheory.HydeLodha.GammaOrbits
import GroupApproximation.GroupTheory.HydeLodha.GammaOrbitsTelescope
import GroupApproximation.Meta.AxiomGuard

/-!
# The residue of `f 0` for `f ∈ Γ₂`

Hyde–Lodha, Lemma 3.9(5) at `x = 0`: if `f ∈ Γ₂` and `0 ≤ f 0 < 1`, then `f 0 ≡ 0` modulo
`5 ℤ[1/6]` (`HigmanThompson.ResEq 4`).  Put `c = f⁻¹ 1 ∈ (0, 1]`.

* `gammaTwo_resEq_preimage_one`: on `[0, c]` both `x` and `f x` have integer part `0`, so condition
  (3) gives slopes `6^i`, and `f t - t` keeps its residue: `c ≡ 1 - f 0`.
* `gammaTwo_resEq_image_zero`: on `[c, 1]` the integer parts are `0` and `1`, so the slopes are
  `2 · 6^i`, and `f t - 2t` keeps its residue; with `f 1 = f 0 + 1` this is `f 0 ≡ 2 (1 - c)`.
* `gammaTwo_resEq_apply_zero`: the two together (`resEq_zero_of_resEq_two_mul_one_sub`).

On each level-`L` grid interval the slope of `f` is read off at the non-dyadic point
`(5k + 1) / (5 · 6^L)` (`hlCond_slope_of_gridPt`).
-/

namespace GroupApproximation
namespace HydeLodha

open HigmanThompson

theorem gridPt_six_mono {L : ℕ} {a b : ℤ} (h : a ≤ b) : gridPt 6 L a ≤ gridPt 6 L b := by
  unfold gridPt
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem gridPt_six_nonneg {L : ℕ} {a : ℤ} (h : 0 ≤ a) : 0 ≤ gridPt 6 L a := by
  unfold gridPt
  have h' : (0 : ℚ) ≤ a := by exact_mod_cast h
  exact div_nonneg h' (by positivity)

theorem gridPt_six_pow (L : ℕ) : gridPt 6 L ((6 : ℤ) ^ L) = 1 := by
  unfold gridPt
  push_cast
  exact div_self (by positivity)

/-- **Slopes from condition (3)** on a level-`L` grid interval on whose interior
`⌊f x⌋ - ⌊x⌋ = d`. -/
theorem hlCond_slope_of_gridPt {f : Equiv.Perm ℚ} (hcond : HLCond f) {L : ℕ} {k : ℤ} {s : ℚ}
    (haff : AffineOn f (gridPt 6 L k) (gridPt 6 L (k + 1)) s) {d : ℤ}
    (hd : ∀ x : ℚ, gridPt 6 L k < x → x < gridPt 6 L (k + 1) → ⌊f x⌋ - ⌊x⌋ = d) :
    ∃ i j : ℤ, s = (2 : ℚ) ^ i * (3 : ℚ) ^ j ∧ i - j = d := by
  have hlo := gridPt_lt_fifth L k
  have hhi := fifth_lt_gridPt_succ L k
  have hnd : ¬ Dyadic6 (((5 * k + 1 : ℤ) : ℚ) / (5 * (6 : ℚ) ^ L)) := by
    intro h
    obtain ⟨M, hM⟩ := h
    exact not_mem_grid_fifth L k M hM
  obtain ⟨a, b, i, j, hax, hxb, haff₂, hij⟩ := hcond _ hnd
  exact ⟨i, j, slope_eq_of_affineOn haff hlo hhi haff₂ hax hxb, by rw [hij]; exact hd _ hlo hhi⟩

/-- **Hyde–Lodha 3.9(5), first half.**  `f⁻¹ 1 ≡ 1 - f 0` modulo `5 ℤ[1/6]`. -/
theorem gammaTwo_resEq_preimage_one {f : Equiv.Perm ℚ} (hf : f ∈ gammaTwo) (h0 : 0 ≤ f 0)
    (h1 : f 0 < 1) : ResEq 4 (f⁻¹ 1) (1 - f 0) := by
  obtain ⟨hPL, hper, hcond⟩ := mem_gammaTwo.mp hf
  obtain ⟨hmono, ⟨N, B, hA⟩, ⟨Ni, Bi, hAi⟩⟩ := (mem_PLGroup 6 slopes23).mp hPL
  obtain ⟨c, hc⟩ : ∃ c : ℚ, c = f⁻¹ 1 := ⟨_, rfl⟩
  rw [← hc]
  have hfc : f c = 1 := by
    rw [hc]
    exact perm_apply_inv_self f 1
  have hf1 : f 1 = f 0 + 1 := by simpa using hper 0
  have hc0 : 0 < c := hmono.lt_iff_lt.mp (by rw [hfc]; exact h1)
  have hc1 : c ≤ 1 := hmono.le_iff_le.mp (by rw [hfc, hf1]; linarith [h0])
  have hone : (1 : ℚ) ∈ Grid 6 0 := ⟨1, by simp⟩
  have hcg : c ∈ Grid 6 (Bi + max 0 Ni) := by
    rw [hc]
    exact hAi.mapsGrid hone
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = max N (Bi + max 0 Ni) := ⟨_, rfl⟩
  have hNL : N ≤ L := by
    rw [hL]
    exact le_max_left _ _
  have hcL : c ∈ Grid 6 L := grid_mono (by rw [hL]; exact le_max_right _ _) hcg
  obtain ⟨K, hK⟩ := hcL
  have hP : ((6 : ℕ) : ℚ) ^ L ≠ 0 := by positivity
  have hcK : c = gridPt 6 L K := by
    unfold gridPt
    exact (eq_div_iff hP).mpr hK
  have hK0 : 0 ≤ K := by
    have h' : (0 : ℚ) ≤ K := by
      rw [← hK]
      exact mul_nonneg hc0.le (by positivity)
    exact_mod_cast h'
  obtain ⟨Kn, hKn⟩ := Int.eq_ofNat_of_zero_le hK0
  have hsteps : ∀ i : ℕ, i < Kn →
      ResEq 4 (f (gridPt 6 L (0 + i + 1)) - ((1 : ℤ) : ℚ) * gridPt 6 L (0 + i + 1))
        (f (gridPt 6 L (0 + i)) - ((1 : ℤ) : ℚ) * gridPt 6 L (0 + i)) := by
    intro i hi
    obtain ⟨s, -, -, haff⟩ := hA.affine_fine hNL (0 + (i : ℤ))
    have hple : gridPt 6 L (0 + (i : ℤ)) ≤ gridPt 6 L (0 + i + 1) := gridPt_six_mono (by omega)
    have hp0 : 0 ≤ gridPt 6 L (0 + (i : ℤ)) := gridPt_six_nonneg (by omega)
    have hqc : gridPt 6 L (0 + i + 1) ≤ c := by
      rw [hcK, hKn]
      exact gridPt_six_mono (by omega)
    obtain ⟨i', j', hs, hij⟩ := hlCond_slope_of_gridPt hcond haff (d := 0) (fun x hlo hhi => by
      have hx0 : 0 ≤ x := by linarith
      have hx1 : x < 1 := by linarith
      have hfx0 : 0 ≤ f x := le_trans h0 (hmono.monotone hx0)
      have hfx1 : f x < 1 := by
        have h' := hmono (lt_of_lt_of_le hhi hqc)
        rw [hfc] at h'
        exact h'
      simp [Int.floor_eq_zero_iff.mpr ⟨hfx0, hfx1⟩, Int.floor_eq_zero_iff.mpr ⟨hx0, hx1⟩])
    have hji : j' = i' := by omega
    have e : (2 : ℚ) ^ i' * (3 : ℚ) ^ i' = (((4 : ℕ) : ℚ) + 2) ^ i' * ((1 : ℤ) : ℚ) := by
      rw [← mul_zpow]
      norm_num
    rw [hs, hji, e] at haff
    have hε : gridPt 6 L (0 + i + 1) - gridPt 6 L (0 + (i : ℤ)) ∈ Grid 6 L :=
      grid_sub (gridPt_mem L _) (gridPt_mem L _)
    exact resEq_of_affineOn_pow hple haff hε
  have ht := resEq_telescope (m := 4)
    (fun k => f (gridPt 6 L k) - ((1 : ℤ) : ℚ) * gridPt 6 L k) 0 Kn hsteps
  have hend : gridPt 6 L (0 + (Kn : ℤ)) = c := by rw [zero_add, ← hKn, ← hcK]
  have hstart : gridPt 6 L 0 = 0 := by simp [gridPt]
  simp only [hend, hstart] at ht
  exact resEq_of_sub_eq ht.symm (by rw [hfc]; push_cast; ring)

/-- **Hyde–Lodha 3.9(5), second half.**  `f 0 ≡ 2 (1 - f⁻¹ 1)` modulo `5 ℤ[1/6]`. -/
theorem gammaTwo_resEq_image_zero {f : Equiv.Perm ℚ} (hf : f ∈ gammaTwo) (h0 : 0 ≤ f 0)
    (h1 : f 0 < 1) : ResEq 4 (f 0) (2 * (1 - f⁻¹ 1)) := by
  obtain ⟨hPL, hper, hcond⟩ := mem_gammaTwo.mp hf
  obtain ⟨hmono, ⟨N, B, hA⟩, ⟨Ni, Bi, hAi⟩⟩ := (mem_PLGroup 6 slopes23).mp hPL
  obtain ⟨c, hc⟩ : ∃ c : ℚ, c = f⁻¹ 1 := ⟨_, rfl⟩
  rw [← hc]
  have hfc : f c = 1 := by
    rw [hc]
    exact perm_apply_inv_self f 1
  have hf1 : f 1 = f 0 + 1 := by simpa using hper 0
  have hc0 : 0 < c := hmono.lt_iff_lt.mp (by rw [hfc]; exact h1)
  have hc1 : c ≤ 1 := hmono.le_iff_le.mp (by rw [hfc, hf1]; linarith [h0])
  have hone : (1 : ℚ) ∈ Grid 6 0 := ⟨1, by simp⟩
  have hcg : c ∈ Grid 6 (Bi + max 0 Ni) := by
    rw [hc]
    exact hAi.mapsGrid hone
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = max N (Bi + max 0 Ni) := ⟨_, rfl⟩
  have hNL : N ≤ L := by
    rw [hL]
    exact le_max_left _ _
  have hcL : c ∈ Grid 6 L := grid_mono (by rw [hL]; exact le_max_right _ _) hcg
  obtain ⟨K, hK⟩ := hcL
  have hP : ((6 : ℕ) : ℚ) ^ L ≠ 0 := by positivity
  have hcK : c = gridPt 6 L K := by
    unfold gridPt
    exact (eq_div_iff hP).mpr hK
  have hKL : K ≤ (6 : ℤ) ^ L := by
    have h' : (K : ℚ) ≤ (6 : ℚ) ^ L := by
      rw [← hK]
      push_cast
      exact mul_le_of_le_one_left (by positivity) hc1
    exact_mod_cast h'
  obtain ⟨Jn, hJn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hKL)
  have hsteps : ∀ i : ℕ, i < Jn →
      ResEq 4 (f (gridPt 6 L (K + i + 1)) - ((2 : ℤ) : ℚ) * gridPt 6 L (K + i + 1))
        (f (gridPt 6 L (K + i)) - ((2 : ℤ) : ℚ) * gridPt 6 L (K + i)) := by
    intro i hi
    obtain ⟨s, -, -, haff⟩ := hA.affine_fine hNL (K + (i : ℤ))
    have hple : gridPt 6 L (K + (i : ℤ)) ≤ gridPt 6 L (K + i + 1) := gridPt_six_mono (by omega)
    have hcp : c ≤ gridPt 6 L (K + (i : ℤ)) := by
      rw [hcK]
      exact gridPt_six_mono (by omega)
    have hq1 : gridPt 6 L (K + i + 1) ≤ 1 := by
      rw [← gridPt_six_pow L]
      exact gridPt_six_mono (by omega)
    obtain ⟨i', j', hs, hij⟩ := hlCond_slope_of_gridPt hcond haff (d := 1) (fun x hlo hhi => by
      have hx0 : 0 ≤ x := by linarith
      have hx1 : x < 1 := by linarith
      have hfx0 : 1 ≤ f x := by
        have h' := hmono (lt_of_le_of_lt hcp hlo)
        rw [hfc] at h'
        exact h'.le
      have hfx1 : f x < 2 := by
        have h' := hmono (lt_of_lt_of_le hhi hq1)
        rw [hf1] at h'
        linarith [h1]
      have hfl : ⌊f x⌋ = 1 :=
        Int.floor_eq_iff.mpr ⟨by exact_mod_cast hfx0, by push_cast; linarith⟩
      simp [hfl, Int.floor_eq_zero_iff.mpr ⟨hx0, hx1⟩])
    obtain rfl : i' = j' + 1 := by omega
    have e : (2 : ℚ) ^ (j' + 1) * (3 : ℚ) ^ j' = (((4 : ℕ) : ℚ) + 2) ^ j' * ((2 : ℤ) : ℚ) := by
      rw [zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0), mul_right_comm, ← mul_zpow]
      norm_num
    rw [hs, e] at haff
    have hε : gridPt 6 L (K + i + 1) - gridPt 6 L (K + (i : ℤ)) ∈ Grid 6 L :=
      grid_sub (gridPt_mem L _) (gridPt_mem L _)
    exact resEq_of_affineOn_pow hple haff hε
  have ht := resEq_telescope (m := 4)
    (fun k => f (gridPt 6 L k) - ((2 : ℤ) : ℚ) * gridPt 6 L k) K Jn hsteps
  have hend : gridPt 6 L (K + (Jn : ℤ)) = 1 := by
    rw [show K + (Jn : ℤ) = (6 : ℤ) ^ L by omega]
    exact gridPt_six_pow L
  have hstart : gridPt 6 L K = c := hcK.symm
  simp only [hend, hstart] at ht
  exact resEq_of_sub_eq ht (by rw [hf1, hfc]; push_cast; ring)

/-- **Hyde–Lodha 3.9(5) at `x = 0`.**  For `f ∈ Γ₂` with `0 ≤ f 0 < 1`, `f 0 ≡ 0` modulo
`5 ℤ[1/6]`. -/
theorem gammaTwo_resEq_apply_zero {f : Equiv.Perm ℚ} (hf : f ∈ gammaTwo) (h0 : 0 ≤ f 0)
    (h1 : f 0 < 1) : ResEq 4 (f 0) 0 :=
  resEq_zero_of_resEq_two_mul_one_sub (gammaTwo_resEq_image_zero hf h0 h1)
    (gammaTwo_resEq_preimage_one hf h0 h1)

#audit_axioms GroupApproximation.HydeLodha.hlCond_slope_of_gridPt
#audit_axioms GroupApproximation.HydeLodha.gammaTwo_resEq_preimage_one
#audit_axioms GroupApproximation.HydeLodha.gammaTwo_resEq_image_zero
#audit_axioms GroupApproximation.HydeLodha.gammaTwo_resEq_apply_zero

end HydeLodha
end GroupApproximation
