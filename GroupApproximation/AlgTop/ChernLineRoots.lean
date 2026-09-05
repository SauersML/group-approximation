import GroupApproximation.AlgTop.ChernPowerSums

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
/-!
# The power sums of a line class are the powers of its Chern root

`GroupApproximation.AlgTop.TotalChern.powerSum` is defined by a logarithmic
derivative, which makes Newton's identity and additivity easy but leaves open
whether it is the classical thing.  It is: on the line class `1 + a X` the power
sums are exactly `a^q`.

Combined with `powerSum_mul`, this says that on a split class `∏ᵢ (1 + aᵢ X)` the
`q`-th power sum is `∑ᵢ aᵢ^q`, so the Chern character `ch_q = p_q / q!` of
`GroupApproximation.AlgTop.TotalChern.chernChar` is the classical
`ch = ∑ᵢ exp(aᵢ)`.  That is the identification a consumer needs before believing
that `chernChar` deserves the name.

The proof is the coefficient recursion of `(1 + aX) · N(1 + aX) = X · a`.

## Main declarations

* `TotalChern.derivativeFun_line` — `(1 + aX)' = a`.
* `TotalChern.coeff_succ_newtonSeries_line` — the Newton series of a line class
  is `∑_{q ≥ 1} (-1)^{q+1} a^q X^q`.
* `TotalChern.powerSum_line` — `p_q(1 + aX) = a^q` for `q > 0`.
-/

namespace GroupApproximation
namespace AlgTop
namespace TotalChern

open scoped PowerSeries

noncomputable section

variable {A : Type*} [CommRing A]

theorem coeff_zero_newtonSeries (c : TotalChern A) :
    PowerSeries.coeff 0 (newtonSeries c) = 0 := by
  rw [newtonSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_mul,
    PowerSeries.constantCoeff_X, zero_mul, zero_mul]

theorem derivativeFun_line (a : A) :
    PowerSeries.derivativeFun (line a).series = PowerSeries.C a := by
  ext n
  rw [PowerSeries.coeff_derivativeFun, line_series, map_add, PowerSeries.coeff_one,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_C]
  rcases n with _ | n
  · simp
  · simp

/-- The coefficient recursion satisfied by the Newton series of a line class:
it is the degree-`(q+1)` coefficient of `(1 + aX) · N = X · a`. -/
theorem coeff_newtonSeries_line_rec (a : A) (q : ℕ) :
    PowerSeries.coeff (q + 1) (newtonSeries (line a))
        + a * PowerSeries.coeff q (newtonSeries (line a))
      = a * (if q + 1 = 1 then (1 : A) else 0) := by
  have hmain : (line a).series * newtonSeries (line a) = PowerSeries.X * PowerSeries.C a := by
    rw [series_mul_newtonSeries, derivativeFun_line]
  have h : PowerSeries.coeff (q + 1) ((line a).series * newtonSeries (line a))
      = PowerSeries.coeff (q + 1) (PowerSeries.X * PowerSeries.C a) := by rw [hmain]
  rwa [line_series, add_mul, one_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_succ_X_mul, mul_comm PowerSeries.X (PowerSeries.C a),
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X] at h

theorem coeff_one_newtonSeries_line (a : A) :
    PowerSeries.coeff 1 (newtonSeries (line a)) = a := by
  have h := coeff_newtonSeries_line_rec a 0
  rw [coeff_zero_newtonSeries, mul_zero, add_zero, if_pos rfl, mul_one] at h
  exact h

theorem coeff_add_two_newtonSeries_line (a : A) (q : ℕ) :
    PowerSeries.coeff (q + 1 + 1) (newtonSeries (line a))
      = -(a * PowerSeries.coeff (q + 1) (newtonSeries (line a))) := by
  have h := coeff_newtonSeries_line_rec a (q + 1)
  rw [if_neg (by omega : ¬ (q + 1 + 1 = 1)), mul_zero] at h
  linear_combination h

theorem coeff_succ_newtonSeries_line (a : A) (q : ℕ) :
    PowerSeries.coeff (q + 1) (newtonSeries (line a))
      = (-1 : A) ^ (q + 1 + 1) * a ^ (q + 1) := by
  induction q with
  | zero =>
      rw [coeff_one_newtonSeries_line]
      norm_num
  | succ q ih =>
      rw [coeff_add_two_newtonSeries_line, ih]
      ring

/-- **The power sums of a line class are the powers of its Chern root.** -/
theorem powerSum_line (a : A) {q : ℕ} (hq : 0 < q) : (line a).powerSum q = a ^ q := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hsign : ((-1 : A) ^ (m + 1 + 1)) * ((-1 : A) ^ (m + 1 + 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [powerSum, coeff_succ_newtonSeries_line, ← mul_assoc, hsign, one_mul]

end

end TotalChern
end AlgTop
end GroupApproximation
