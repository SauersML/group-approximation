import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import GroupApproximation.Meta.AxiomGuard

/-!
# A linear budget for balanced polygon cuts

The additive size of a polygon cut is its number of sides minus four.
Quarter-separated cuts split this size into two positive parts, each at most
seven eighths of the parent. The square-root debit in `cutPotential` pays for
the logarithmic length of the new diagonal at every step of the recursion.
-/

namespace GroupApproximation.Olshanskii

/-- The potential reserved for geometric cut lengths. -/
noncomputable def cutPotential (n : ℕ) : ℝ :=
  40000 * (n - 4 : ℕ) - 20000 * Real.sqrt (n - 4 : ℕ)

private theorem square_le_four_mul_two_pow (k : ℕ) :
    (k + 1) ^ 2 ≤ 4 * 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rcases lt_or_ge k 2 with hk | hk
    · interval_cases k <;> norm_num
    · rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k]
      nlinarith

/-- A coarse square-root bound suffices; no asymptotic threshold is needed. -/
theorem clog_add_one_le_eight_sqrt_size {n : ℕ} (hn : 9 ≤ n) :
    (Nat.clog 2 n : ℝ) + 1 ≤ 8 * Real.sqrt (n - 4 : ℕ) := by
  let k := Nat.clog 2 n
  have hk : 0 < k := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr
    simpa using (show 1 < n by omega)
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2)
    (show 1 < n by omega)
  have hpow : 2 ^ k < 2 * n := by
    have he : k = (k - 1) + 1 := by omega
    rw [he, Nat.pow_succ]
    change 2 ^ (k - 1) < n at hp
    nlinarith
  have hsq := square_le_four_mul_two_pow k
  have hnat : (k + 1) ^ 2 ≤ 64 * (n - 4) := by omega
  have hreal : ((k : ℝ) + 1) ^ 2 ≤ 64 * (n - 4 : ℕ) := by
    exact_mod_cast hnat
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (n - 4 : ℕ) by positivity)
  have hs0 := Real.sqrt_nonneg (n - 4 : ℕ)
  change (k : ℝ) + 1 ≤ _
  nlinarith

/-- The square-root mass increases by at least one twentieth at a cut. -/
theorem balanced_size_sqrt_gain {n m : ℕ} (hn : 9 ≤ n)
    (hlow : n ≤ 4 * m) (hhigh : 4 * m ≤ 3 * n) :
    (21 / 20 : ℝ) * Real.sqrt (n - 4 : ℕ) ≤
      Real.sqrt (m - 2 : ℕ) + Real.sqrt (n - m - 2 : ℕ) := by
  have hsum : (m - 2) + (n - m - 2) = n - 4 := by omega
  have hsmall₁ : 8 * (m - 2) ≤ 7 * (n - 4) := by omega
  have hdecomp : (n - m - 2) + m + 2 = n := by omega
  have hsmall₂ : 8 * (n - m - 2) ≤ 7 * (n - 4) := by
    rcases lt_or_ge n 12 with hn12 | hn12
    · interval_cases n <;> omega
    · omega
  have h₁ : (m - 2 : ℕ) ≤ (7 / 8 : ℝ) * (n - 4 : ℕ) := by
    have hr : (8 : ℝ) * (m - 2 : ℕ) ≤ 7 * (n - 4 : ℕ) := by exact_mod_cast hsmall₁
    linarith
  have h₂ : (n - m - 2 : ℕ) ≤ (7 / 8 : ℝ) * (n - 4 : ℕ) := by
    have hr : (8 : ℝ) * (n - m - 2 : ℕ) ≤ 7 * (n - 4 : ℕ) := by exact_mod_cast hsmall₂
    linarith
  have hsR : ((m - 2 : ℕ) : ℝ) + (n - m - 2 : ℕ) = (n - 4 : ℕ) := by
    exact_mod_cast hsum
  have hN : (0 : ℝ) < (n - 4 : ℕ) := by exact_mod_cast (show 0 < n - 4 by omega)
  have hsn := Real.sqrt_pos.mpr hN
  have hsa := Real.sqrt_nonneg (m - 2 : ℕ)
  have hsb := Real.sqrt_nonneg (n - m - 2 : ℕ)
  have hsα := Real.sqrt_nonneg (7 / 8 : ℝ)
  have hqα := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 8)
  have hgain : Real.sqrt (7 / 8 : ℝ) * (21 / 20) ≤ 1 := by nlinarith
  have hper₁ := Real.sqrt_le_sqrt h₁
  have hper₂ := Real.sqrt_le_sqrt h₂
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7 / 8)] at hper₁ hper₂
  have hq₁ := Real.sq_sqrt (show (0 : ℝ) ≤ (m - 2 : ℕ) by positivity)
  have hq₂ := Real.sq_sqrt (show (0 : ℝ) ≤ (n - m - 2 : ℕ) by positivity)
  have hqN := Real.sq_sqrt (le_of_lt hN)
  have hmass : Real.sqrt (n - 4 : ℕ) ≤
      (Real.sqrt (m - 2 : ℕ) + Real.sqrt (n - m - 2 : ℕ)) *
        Real.sqrt (7 / 8 : ℝ) := by
    have hmul₁ := mul_le_mul_of_nonneg_left hper₁ hsa
    have hmul₂ := mul_le_mul_of_nonneg_left hper₂ hsb
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hgain (add_nonneg hsa hsb)
  nlinarith

/-- The debit pays for both copies of a diagonal and the coefficient eight
used in the short-class estimate. -/
theorem cutPotential_subdivision {n m : ℕ} (hn : 9 ≤ n)
    (hlow : n ≤ 4 * m) (hhigh : 4 * m ≤ 3 * n) :
    cutPotential (m + 2) + cutPotential (n - m + 2) +
      96 * ((Nat.clog 2 n : ℝ) + 1) + 16 ≤ cutPotential n := by
  have hsum : (m - 2) + (n - m - 2) = n - 4 := by omega
  have hsumR : ((m - 2 : ℕ) : ℝ) + (n - m - 2 : ℕ) = (n - 4 : ℕ) := by
    exact_mod_cast hsum
  have hlog := clog_add_one_le_eight_sqrt_size hn
  have hgain := balanced_size_sqrt_gain hn hlow hhigh
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n - 4 : ℕ) := by
    apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
    exact_mod_cast (show 1 ≤ n - 4 by omega)
  simp only [cutPotential,
    show m + 2 - 4 = m - 2 by omega,
    show n - m + 2 - 4 = n - m - 2 by omega]
  linarith

theorem cutPotential_base {n : ℕ} (hn : 5 ≤ n) (hn8 : n ≤ 8) :
    48 * (n : ℝ) * ((n : ℝ) - 1) ≤ cutPotential n := by
  have hN : (1 : ℝ) ≤ (n - 4 : ℕ) := by exact_mod_cast (show 1 ≤ n - 4 by omega)
  have hs : Real.sqrt (n - 4 : ℕ) ≤ (n - 4 : ℕ) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  have hnR : (n : ℝ) ≤ 8 := by exact_mod_cast hn8
  have hn0 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hprod := mul_le_mul (show (n : ℝ) ≤ 8 from hnR)
    (show (n : ℝ) - 1 ≤ 7 by linarith) (show 0 ≤ (n : ℝ) - 1 by linarith)
    (by norm_num : (0 : ℝ) ≤ 8)
  unfold cutPotential
  nlinarith

theorem cutPotential_le (n : ℕ) : cutPotential n ≤ 40000 * n := by
  have hs := Real.sqrt_nonneg (n - 4 : ℕ)
  have hN : ((n - 4 : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.sub_le n 4)
  unfold cutPotential
  linarith

end GroupApproximation.Olshanskii

#audit_axioms GroupApproximation.Olshanskii.clog_add_one_le_eight_sqrt_size
#audit_axioms GroupApproximation.Olshanskii.balanced_size_sqrt_gain
#audit_axioms GroupApproximation.Olshanskii.cutPotential_subdivision
#audit_axioms GroupApproximation.Olshanskii.cutPotential_base
#audit_axioms GroupApproximation.Olshanskii.cutPotential_le
