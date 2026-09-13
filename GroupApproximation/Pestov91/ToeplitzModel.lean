import GroupApproximation.Pestov91.Subshift
import Mathlib.Data.ZMod.Basic

/-!
# Periodic models of the Toeplitz subshift

`toeplitzModel K n` is the parity of `min (ν₂(3 n - 1)) K`, a `2 ^ K`-periodic sequence. Every
window of length `L ≤ 2 ^ K` of the model occurs in `toeplitz`. Conversely, if `L ≤ 2 ^ K₀`, every
window of `toeplitz` of length `L` occurs in the model with `K = K₀ + 2`. In both directions the
at most one position of high valuation in a window is moved by a multiple of `2 ^ K` (or `2 ^ K₀`)
to a position of the right valuation.
-/

namespace GroupApproximation.Pestov91

/-- The periodic Toeplitz model: the parity of `min (ν₂(3 n - 1)) K`. -/
def toeplitzModel (K : ℕ) (n : ℤ) : Bool := decide (min (padicValInt 2 (3 * n - 1)) K % 2 = 1)

theorem decide_mod_two_congr {u v : ℕ} (h : u % 2 = v % 2) :
    decide (u % 2 = 1) = decide (v % 2 = 1) := by
  rw [h]

theorem val_ge_of_dvd {n : ℤ} {K : ℕ} (h : (2 : ℤ) ^ K ∣ 3 * n - 1) :
    K ≤ padicValInt 2 (3 * n - 1) :=
  (two_pow_dvd_iff_le_val (three_mul_sub_one_ne_zero n) K).mp h

theorem val_lt_of_not_dvd {n : ℤ} {K : ℕ} (h : ¬ (2 : ℤ) ^ K ∣ 3 * n - 1) :
    padicValInt 2 (3 * n - 1) < K := by
  rw [two_pow_dvd_iff_le_val (three_mul_sub_one_ne_zero n)] at h
  omega

theorem toeplitzModel_add_two_pow_mul (K : ℕ) (n t : ℤ) :
    toeplitzModel K (n + 2 ^ K * t) = toeplitzModel K n := by
  have e : 3 * (n + 2 ^ K * t) - 1 = (3 * n - 1) + 2 ^ K * (3 * t) := by ring
  unfold toeplitzModel
  rw [e]
  by_cases h : (2 : ℤ) ^ K ∣ 3 * n - 1
  · have h1 := val_ge_of_dvd h
    have h2 : K ≤ padicValInt 2 ((3 * n - 1) + 2 ^ K * (3 * t)) := by
      refine (two_pow_dvd_iff_le_val ?_ K).mp (dvd_add h (dvd_mul_right _ _))
      rw [← e]
      exact three_mul_sub_one_ne_zero _
    exact decide_mod_two_congr (by omega)
  · rw [val_add_two_pow_mul (three_mul_sub_one_ne_zero n) (val_lt_of_not_dvd h)]

/-- (A) Every window of the model occurs in `toeplitz`. -/
theorem toeplitz_window_of_model {K L : ℕ} (hL : L ≤ 2 ^ K) (a : ℤ) :
    ∃ c : ℤ, ∀ i : ℕ, i < L → toeplitz (c + i) = toeplitzModel K (a + i) := by
  have hL' : (L : ℤ) ≤ 2 ^ K := by exact_mod_cast hL
  by_cases hex : ∃ i0 : ℕ, i0 < L ∧ (2 : ℤ) ^ K ∣ 3 * (a + i0) - 1
  · obtain ⟨i0, hi0, s, hs⟩ := hex
    refine ⟨a + 2 ^ K * (1 - s), fun i hi => ?_⟩
    rw [show a + 2 ^ K * (1 - s) + i = (a + i) + 2 ^ K * (1 - s) by ring]
    by_cases hii : i = i0
    · rw [hii]
      have v1 : padicValInt 2 (3 * (a + i0 + 2 ^ K * (1 - s)) - 1) = K := by
        rw [show 3 * (a + i0 + 2 ^ K * (1 - s)) - 1 = 2 ^ K * (3 - 2 * s) by
          linear_combination hs]
        exact val_two_pow_mul (by omega) K
      have v2 := val_ge_of_dvd (Dvd.intro s hs.symm)
      unfold toeplitz toeplitzModel
      rw [v1]
      exact decide_mod_two_congr (by omega)
    · have hnd : ¬ (2 : ℤ) ^ K ∣ 3 * (a + i) - 1 := by
        intro hd
        apply hii
        have := eq_of_two_pow_dvd hd (Dvd.intro s hs.symm) (by omega) (by omega)
        omega
      have hv := val_lt_of_not_dvd hnd
      rw [toeplitz_add_two_pow_mul hv]
      unfold toeplitz toeplitzModel
      exact decide_mod_two_congr (by omega)
  · refine ⟨a, fun i hi => ?_⟩
    have hv := val_lt_of_not_dvd (n := a + i) fun hd => hex ⟨i, hi, hd⟩
    unfold toeplitz toeplitzModel
    exact decide_mod_two_congr (by omega)

/-- (B) Every window of `toeplitz` occurs in the model. -/
theorem model_window_of_toeplitz {K0 L : ℕ} (hL : L ≤ 2 ^ K0) (c : ℤ) :
    ∃ a : ℤ, ∀ i : ℕ, i < L → toeplitzModel (K0 + 2) (a + i) = toeplitz (c + i) := by
  have hL' : (L : ℤ) ≤ 2 ^ K0 := by exact_mod_cast hL
  by_cases hex : ∃ i0 : ℕ, i0 < L ∧ (2 : ℤ) ^ K0 ∣ 3 * (c + i0) - 1
  · obtain ⟨i0, hi0, s, hs⟩ := hex
    obtain ⟨t, ht⟩ : ∃ t : ℤ, padicValInt 2 (3 * (c + i0 + 2 ^ K0 * t) - 1) % 2
        = padicValInt 2 (3 * (c + i0) - 1) % 2 ∧
        padicValInt 2 (3 * (c + i0 + 2 ^ K0 * t) - 1) < K0 + 2 := by
      rcases Nat.mod_two_eq_zero_or_one (padicValInt 2 (3 * (c + i0) - 1) + K0) with hp | hp
      · refine ⟨1 - s, ?_⟩
        have v1 : padicValInt 2 (3 * (c + i0 + 2 ^ K0 * (1 - s)) - 1) = K0 := by
          rw [show 3 * (c + i0 + 2 ^ K0 * (1 - s)) - 1 = 2 ^ K0 * (3 - 2 * s) by
            linear_combination hs]
          exact val_two_pow_mul (by omega) K0
        rw [v1]
        constructor <;> omega
      · refine ⟨6 - 3 * s, ?_⟩
        have v1 : padicValInt 2 (3 * (c + i0 + 2 ^ K0 * (6 - 3 * s)) - 1) = K0 + 1 := by
          rw [show 3 * (c + i0 + 2 ^ K0 * (6 - 3 * s)) - 1 = 2 ^ (K0 + 1) * (9 - 4 * s) by
            linear_combination hs]
          exact val_two_pow_mul (by omega) (K0 + 1)
        rw [v1]
        constructor <;> omega
    refine ⟨c + 2 ^ K0 * t, fun i hi => ?_⟩
    rw [show c + 2 ^ K0 * t + i = (c + i) + 2 ^ K0 * t by ring]
    by_cases hii : i = i0
    · rw [hii]
      unfold toeplitz toeplitzModel
      exact decide_mod_two_congr (by omega)
    · have hnd : ¬ (2 : ℤ) ^ K0 ∣ 3 * (c + i) - 1 := by
        intro hd
        apply hii
        have := eq_of_two_pow_dvd hd (Dvd.intro s hs.symm) (by omega) (by omega)
        omega
      have hv := val_lt_of_not_dvd hnd
      have e : 3 * ((c + i) + 2 ^ K0 * t) - 1 = (3 * (c + i) - 1) + 2 ^ K0 * (3 * t) := by ring
      unfold toeplitz toeplitzModel
      rw [e, val_add_two_pow_mul (three_mul_sub_one_ne_zero _) hv]
      exact decide_mod_two_congr (by omega)
  · refine ⟨c, fun i hi => ?_⟩
    have hv := val_lt_of_not_dvd (n := c + i) fun hd => hex ⟨i, hi, hd⟩
    unfold toeplitz toeplitzModel
    exact decide_mod_two_congr (by omega)

theorem toeplitzModel_emod (K : ℕ) (m : ℤ) : toeplitzModel K (m % 2 ^ K) = toeplitzModel K m := by
  rw [Int.emod_def, sub_eq_add_neg, ← mul_neg, toeplitzModel_add_two_pow_mul]

/-- The model as a function on `ZMod (2 ^ K)`. -/
def toeplitzModelZMod (K : ℕ) (x : ZMod (2 ^ K)) : Bool := toeplitzModel K (x.val : ℤ)

theorem toeplitzModelZMod_intCast (K : ℕ) (m : ℤ) :
    toeplitzModelZMod K (m : ZMod (2 ^ K)) = toeplitzModel K m := by
  haveI : NeZero (2 ^ K) := ⟨by positivity⟩
  unfold toeplitzModelZMod
  rw [ZMod.val_intCast]
  push_cast
  exact toeplitzModel_emod K m

/-- A periodic model of the Toeplitz subshift at radius `ρ`. -/
theorem exists_periodic_model (ρ : ℕ) :
    ∃ N : ℕ, 2 * ρ + 1 < N ∧ ∃ p : ZMod N → Bool,
      (∀ n : ZMod N, ∃ z : X, ∀ k : ℤ, |k| ≤ ρ → z.1 k = p (n + k)) ∧
      (∀ y : X, ∃ n : ZMod N, ∀ k : ℤ, |k| ≤ ρ → y.1 k = p (n + k)) := by
  have hL0 : 2 * ρ + 1 < 2 ^ (2 * ρ + 1) := Nat.lt_two_pow_self
  have hL1 : 2 * ρ + 1 < 2 ^ (2 * ρ + 1 + 2) := by
    have : 2 ^ (2 * ρ + 1) ≤ 2 ^ (2 * ρ + 1 + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  refine ⟨2 ^ (2 * ρ + 1 + 2), hL1, toeplitzModelZMod (2 * ρ + 1 + 2), fun n => ?_, fun y => ?_⟩
  · obtain ⟨m, rfl⟩ := ZMod.intCast_surjective n
    obtain ⟨c, hc⟩ := toeplitz_window_of_model hL1.le (m - ρ)
    refine ⟨shiftBy (c + ρ) toeplitzPoint, fun k hk => ?_⟩
    rw [abs_le] at hk
    have hi := hc (k + ρ).toNat (by omega)
    rw [shiftBy_apply, ← Int.cast_add, toeplitzModelZMod_intCast,
      show c + (ρ : ℤ) + k = c + ((k + ρ).toNat : ℕ) by omega,
      show m + k = m - ρ + ((k + ρ).toNat : ℕ) by omega]
    exact hi
  · obtain ⟨b, hb⟩ := mem_window y (-ρ) (2 * ρ + 1)
    obtain ⟨a, ha⟩ := model_window_of_toeplitz hL0.le b
    refine ⟨((a + ρ : ℤ) : ZMod (2 ^ (2 * ρ + 1 + 2))), fun k hk => ?_⟩
    rw [abs_le] at hk
    have h1 := hb (k + ρ).toNat (by omega)
    have h2 := ha (k + ρ).toNat (by omega)
    have e : -(ρ : ℤ) + ((k + ρ).toNat : ℕ) = k := by omega
    rw [e] at h1
    rw [← Int.cast_add, toeplitzModelZMod_intCast,
      show a + (ρ : ℤ) + k = a + ((k + ρ).toNat : ℕ) by omega, h2]
    exact h1

end GroupApproximation.Pestov91
