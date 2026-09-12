import Mathlib.Analysis.SpecificLimits.Normed
import GroupApproximation.KunThom.KunThomParameters

/-!
# Numerical parameters for improving cluster candidates

`KunThomParameters.exists_improvementParameters` produces a Markov step count
`k`, a goodness level `η`, a transfer tolerance `δ` and a boundary level `β`
for rounding products of almost centralizers.  Improving a composite of two
cluster candidates needs the same four quantities with a different balance:
the boundary level must be a prescribed small multiple `p η` of the goodness
level, and both `η` and `k² η` must lie below a prescribed threshold `ζ`.  The
proof is the same: exponential Kazhdan contraction beats every polynomial cost.
-/

namespace GroupApproximation
namespace CentralizerNormalizationParameters

open Filter
open scoped Topology

/-- Parameters for candidate improvement.  The boundary level is `p * η`. -/
theorem exists_repairParameters {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (s : ℕ) (hs : 0 < s) {p ζ : ℝ} (hp : 0 < p) (hζ : 0 < ζ) :
    ∃ (k : ℕ) (η δ : ℝ),
      0 < k ∧ 0 < η ∧ 0 < δ ∧ η < ζ ∧ (k : ℝ) ^ 2 * η < ζ ∧
      16 * (s : ℝ) ^ 4 * (16 * q ^ (2 * k) * (s : ℝ)⁻¹ * η + δ) <
        (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
          (p * η) ^ 4 := by
  let r : ℝ := (q + 1) / 2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hsReal : (0 : ℝ) < s := by exact_mod_cast hs
  let coarea : ℝ :=
    ((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2
  have hcoarea : 0 < coarea := by dsimp [coarea]; norm_num
  let C : ℝ :=
    16 * (s : ℝ) ^ 4 * (16 * (s : ℝ)⁻¹ + 1)
  let D : ℝ := coarea ^ 2 * p ^ 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hrpow : Tendsto (fun m : ℕ ↦ r ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hrpoly : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ 2 * r ^ m) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0.le hr1
  have heventEta : ∀ᶠ m : ℕ in atTop, r ^ m < ζ :=
    (tendsto_order.1 hrpow).2 _ hζ
  have heventPoly : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ 2 * r ^ m < ζ / 4 :=
    (tendsto_order.1 hrpoly).2 _ (div_pos hζ (by norm_num))
  have heventNumerical : ∀ᶠ m : ℕ in atTop, r ^ m < D / C :=
    (tendsto_order.1 hrpow).2 _ (div_pos hD hC)
  have heventPositive : ∀ᶠ m : ℕ in atTop, 1 ≤ m := eventually_ge_atTop 1
  have hall : ∀ᶠ m : ℕ in atTop,
      1 ≤ m ∧ r ^ m < ζ ∧ (m : ℝ) ^ 2 * r ^ m < ζ / 4 ∧ r ^ m < D / C := by
    filter_upwards [heventPositive, heventEta, heventPoly, heventNumerical]
      with m hm hη hpoly hnum
    exact ⟨hm, hη, hpoly, hnum⟩
  obtain ⟨m, hm, hηsmall, hpoly, hnum⟩ := hall.exists
  let k : ℕ := 2 * m
  let η : ℝ := r ^ m
  let δ : ℝ := r ^ (5 * m)
  have hk : 0 < k := by dsimp [k]; omega
  have hη : 0 < η := by dsimp [η]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨k, η, δ, hk, hη, hδ, ?_, ?_, ?_⟩
  · exact hηsmall
  · dsimp [k, η]
    push_cast
    nlinarith
  · have hqpow : q ^ (4 * m) ≤ r ^ (4 * m) := by
      gcongr
    have hqterm : q ^ (4 * m) * r ^ m ≤ r ^ (5 * m) := by
      calc
        q ^ (4 * m) * r ^ m ≤ r ^ (4 * m) * r ^ m :=
          mul_le_mul_of_nonneg_right hqpow (pow_nonneg hr0.le _)
        _ = r ^ (5 * m) := by
          rw [← pow_add]
          congr 1
          omega
    have hinv : 0 ≤ (s : ℝ)⁻¹ := inv_nonneg.mpr hsReal.le
    have hinner :
        16 * q ^ (4 * m) * (s : ℝ)⁻¹ * r ^ m + r ^ (5 * m) ≤
          (16 * (s : ℝ)⁻¹ + 1) * r ^ (5 * m) := by
      have hscaled :
          (16 * (s : ℝ)⁻¹) * (q ^ (4 * m) * r ^ m) ≤
            (16 * (s : ℝ)⁻¹) * r ^ (5 * m) :=
        mul_le_mul_of_nonneg_left hqterm
          (mul_nonneg (by norm_num) hinv)
      calc
        16 * q ^ (4 * m) * (s : ℝ)⁻¹ * r ^ m + r ^ (5 * m) =
            (16 * (s : ℝ)⁻¹) * (q ^ (4 * m) * r ^ m) +
              r ^ (5 * m) := by ring
        _ ≤ (16 * (s : ℝ)⁻¹) * r ^ (5 * m) + r ^ (5 * m) := by
          linarith
        _ = (16 * (s : ℝ)⁻¹ + 1) * r ^ (5 * m) := by ring
    have hleft :
        16 * (s : ℝ) ^ 4 *
            (16 * q ^ (4 * m) * (s : ℝ)⁻¹ * r ^ m + r ^ (5 * m)) ≤
          C * r ^ (5 * m) := by
      have hout0 : 0 ≤ 16 * (s : ℝ) ^ 4 :=
        mul_nonneg (by norm_num) (pow_nonneg hsReal.le 4)
      have hscaled := mul_le_mul_of_nonneg_left hinner hout0
      simpa [C, mul_assoc] using hscaled
    have hCr : C * r ^ m < D := by
      rw [lt_div_iff₀ hC] at hnum
      simpa [mul_comm] using hnum
    have hmiddle : C * r ^ (5 * m) < D * r ^ (4 * m) := by
      have hmul := mul_lt_mul_of_pos_right hCr (pow_pos hr0 (4 * m))
      calc
        C * r ^ (5 * m) = (C * r ^ m) * r ^ (4 * m) := by
          rw [show 5 * m = m + 4 * m by omega, pow_add]
          ring
        _ < D * r ^ (4 * m) := hmul
    calc
      16 * (s : ℝ) ^ 4 *
          (16 * q ^ (2 * k) * (s : ℝ)⁻¹ * η + δ) =
        16 * (s : ℝ) ^ 4 *
          (16 * q ^ (4 * m) * (s : ℝ)⁻¹ * r ^ m + r ^ (5 * m)) := by
            have hexp : 2 * k = 4 * m := by dsimp [k]; omega
            dsimp [η, δ]
            rw [hexp]
      _ ≤ C * r ^ (5 * m) := hleft
      _ < D * r ^ (4 * m) := hmiddle
      _ = coarea ^ 2 * (p * η) ^ 4 := by
        dsimp [D, η]
        ring
      _ = (((1 : ℝ) / 3) *
          (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 * (p * η) ^ 4 := by
        rfl

end CentralizerNormalizationParameters
end GroupApproximation
