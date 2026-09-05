import GroupApproximation.AlgTop.ChernSeries
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Power sums of a total Chern class, and Newton's identity for virtual classes

The square-zero step of the STW Problem LIX manuscript needs Newton's identity
for the **virtual** class `δ = [W] - [p^*V]`, which is not a bundle and has no
Chern roots.  This file removes that obstacle entirely: it attaches power sums to
*every* element of `TotalChern A`, by the logarithmic derivative

```text
N(c) = X · c' / c ∈ A⟦X⟧,      p_q(c) = (-1)^{q+1} · coeff q (N c),
```

and proves

* `newtonSeries_mul` — `N(c d) = N(c) + N(d)`, so `p_q` is **additive** on the
  group `TotalChern A`.  This is the Chern character's defining property at this
  level, and it is exactly the reason the power sums of a formal difference make
  sense: `p_q(W / V) = p_q(W) - p_q(V)`.
* `natCast_mul_chernClass` — **Newton's identity**, unconditionally, for every
  `c : TotalChern A`.  There is no splitting hypothesis: it is the coefficientwise
  form of `c · N(c) = X c'`.
* `natCast_mul_chernClass_of_squareZero` — the manuscript's (2.7) with Newton's
  identity discharged, leaving only the square-zero hypothesis that `z² = 0`
  supplies.
* `powerSum_line` — on a line class the power sums are the powers of the Chern
  root, `p_q(1 + aX) = a^q`, which is what identifies `p_q` with `q! ch_q`.

Everything is an identity of formal power series; there is no topology.
-/

namespace GroupApproximation
namespace AlgTop
namespace TotalChern

open Finset (antidiagonal mem_antidiagonal)
open scoped PowerSeries

noncomputable section

variable {A : Type*} [CommRing A]

theorem series_mul_inv_series (c : TotalChern A) : c.series * c⁻¹.series = 1 := by
  have h := congrArg TotalChern.series (mul_inv_cancel c)
  rwa [mul_series, one_series] at h

/-- The **Newton series** (logarithmic derivative) `X · c' / c` of a total Chern
class. -/
def newtonSeries (c : TotalChern A) : PowerSeries A :=
  PowerSeries.X * PowerSeries.derivativeFun c.series * c⁻¹.series

theorem series_mul_newtonSeries (c : TotalChern A) :
    c.series * newtonSeries c = PowerSeries.X * PowerSeries.derivativeFun c.series := by
  have h := series_mul_inv_series c
  rw [newtonSeries]
  calc c.series *
        (PowerSeries.X * PowerSeries.derivativeFun c.series * c⁻¹.series)
      = (PowerSeries.X * PowerSeries.derivativeFun c.series) *
          (c.series * c⁻¹.series) := by ring
    _ = PowerSeries.X * PowerSeries.derivativeFun c.series := by rw [h, mul_one]

/-- The Newton series turns the group multiplication into addition. -/
theorem newtonSeries_mul (c d : TotalChern A) :
    newtonSeries (c * d) = newtonSeries c + newtonSeries d := by
  have hc := series_mul_inv_series c
  have hd := series_mul_inv_series d
  have hinv : (c * d)⁻¹.series = c⁻¹.series * d⁻¹.series := by
    rw [← mul_series, mul_inv]
  rw [newtonSeries, newtonSeries, newtonSeries, mul_series, hinv,
    PowerSeries.derivativeFun_mul]
  simp only [smul_eq_mul]
  linear_combination
    (PowerSeries.X * PowerSeries.derivativeFun d.series * d⁻¹.series) * hc +
      (PowerSeries.X * PowerSeries.derivativeFun c.series * c⁻¹.series) * hd

@[simp] theorem newtonSeries_one : newtonSeries (1 : TotalChern A) = 0 := by
  rw [newtonSeries, one_series, PowerSeries.derivativeFun_one, mul_zero, zero_mul]

/-- The `q`-th **power sum** of a total Chern class.  For a split class this is
`∑ᵢ aᵢ^q` in the Chern roots (`powerSum_line` is the rank-one case), so it is
`q!` times the degree-`q` part of the Chern character. -/
def powerSum (c : TotalChern A) (q : ℕ) : A :=
  (-1) ^ (q + 1) * PowerSeries.coeff q (newtonSeries c)

@[simp] theorem powerSum_zero (c : TotalChern A) : c.powerSum 0 = 0 := by
  rw [powerSum, newtonSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_mul,
    PowerSeries.constantCoeff_X, zero_mul, zero_mul, mul_zero]

/-- **Additivity of the power sums.**  This is what makes `p_q(W / V)` meaningful
for a formal difference of bundles. -/
theorem powerSum_mul (c d : TotalChern A) (q : ℕ) :
    (c * d).powerSum q = c.powerSum q + d.powerSum q := by
  rw [powerSum, powerSum, powerSum, newtonSeries_mul, map_add, mul_add]

theorem powerSum_div (W V : TotalChern A) (q : ℕ) :
    (W / V).powerSum q = W.powerSum q - V.powerSum q := by
  have h : V.powerSum q + (W / V).powerSum q = W.powerSum q := by
    rw [← powerSum_mul, mul_div_cancel_virtual]
  linear_combination h

/-- **Newton's identity**, for every total Chern class, with no splitting
hypothesis.  It is the degree-`q` coefficient of `c · N(c) = X c'`. -/
theorem natCast_mul_chernClass (c : TotalChern A) (q : ℕ) :
    (q : A) * c.chernClass q
      = ∑ ij ∈ antidiagonal q,
          c.chernClass ij.1 * ((-1) ^ (ij.2 + 1) * c.powerSum ij.2) := by
  have hcoeff := congrArg (fun f => PowerSeries.coeff q f) (series_mul_newtonSeries c)
  simp only at hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  have hright : PowerSeries.coeff q (PowerSeries.X * PowerSeries.derivativeFun c.series)
      = (q : A) * c.chernClass q := by
    rcases q with _ | m
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_X,
        zero_mul]
      simp
    · rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, chernClass]
      push_cast
      ring
  rw [← hright, hcoeff]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [powerSum, chernClass]
  rw [← mul_assoc, ← mul_assoc]
  have hsign : ((-1 : A) ^ (ij.2 + 1)) * ((-1 : A) ^ (ij.2 + 1)) = 1 := by
    rw [← pow_add, ← two_mul]
    simp [pow_mul]
  calc PowerSeries.coeff ij.1 c.series * PowerSeries.coeff ij.2 (newtonSeries c)
      = PowerSeries.coeff ij.1 c.series *
          (((-1 : A) ^ (ij.2 + 1)) * ((-1 : A) ^ (ij.2 + 1)) *
            PowerSeries.coeff ij.2 (newtonSeries c)) := by rw [hsign, one_mul]
    _ = PowerSeries.coeff ij.1 c.series * (-1 : A) ^ (ij.2 + 1) *
          ((-1 : A) ^ (ij.2 + 1) * PowerSeries.coeff ij.2 (newtonSeries c)) := by ring

/-- **(2.7), with Newton's identity discharged.**  If every product of a positive
Chern class with a positive power sum vanishes — which is what `z² = 0` gives in
the manuscript — then `q · c_q = (-1)^{q+1} p_q`. -/
theorem natCast_mul_chernClass_of_squareZero (c : TotalChern A)
    (hsq : ∀ i j, 0 < i → 0 < j → c.chernClass i * c.powerSum j = 0)
    {q : ℕ} (hq : 0 < q) :
    (q : A) * c.chernClass q = (-1) ^ (q + 1) * c.powerSum q := by
  rw [natCast_mul_chernClass c q]
  have hmem : ((0, q) : ℕ × ℕ) ∈ antidiagonal q := mem_antidiagonal.2 (by simp)
  have h₀ : ∀ b ∈ antidiagonal q, b ≠ (0, q) →
      c.chernClass b.1 * ((-1 : A) ^ (b.2 + 1) * c.powerSum b.2) = 0 := by
    rintro ⟨i, j⟩ hb hne
    rw [mem_antidiagonal] at hb
    simp only at hb ⊢
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hj, powerSum_zero, mul_zero, mul_zero]
    · have hi : 0 < i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · refine absurd ?_ hne
          simp only [Prod.mk.injEq]
          exact ⟨h, by omega⟩
        · exact h
      rw [← mul_assoc, mul_comm (c.chernClass i), mul_assoc, hsq i j hi hj, mul_zero]
  rw [Finset.sum_eq_single (0, q) h₀ (fun h => absurd hmem h)]
  simp

end

end TotalChern
end AlgTop
end GroupApproximation
