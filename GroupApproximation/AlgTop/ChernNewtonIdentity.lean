import GroupApproximation.AlgTop.ChernPowerSums
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
/-!
# Newton's identity for a total Chern class, discharged

The parity chain of the STW Problem LIX manuscript needs Newton's identity for
the *virtual* class `δ = [W] - [p^*V]`, and it is standard to take that as a
hypothesis on the grounds that deriving it is the splitting principle and
therefore topology.  It is not: for the encoding of
`GroupApproximation.AlgTop.TotalChern` — a total Chern class is a normalized
power series, and a virtual class is a quotient of two of them — Newton's
identity is the degree-`q` coefficient of the logarithmic-derivative identity

```text
c · N(c) = X · c',      N(c) = X c' / c,
```

which holds for **every** element of the group `TotalChern A`, split or not.
This file converts `GroupApproximation.AlgTop.TotalChern.natCast_mul_chernClass`
into the `Finset.range` shape in which the parity chain states Newton's identity,
so that the hypothesis can be replaced by a theorem.  The replacement itself is
`GroupApproximation.AlgTop.TotalChern.chernClass_eq_of_chernChar_sq_zero`.

The Chern character is defined here from the power sums by `ch_q = p_q / q!`,
which needs the coefficients to be a `ℚ`-algebra — the same hypothesis the parity
chain already carries for the same reason, since it has to divide Newton's
identity by `q`.

This file imports nothing from the parity lane, so the two stay independently
buildable.

## Main declarations

* `TotalChern.chernChar` — `ch_q = p_q / q!`.
* `TotalChern.factorial_mul_chernChar` — `q! · ch_q = p_q`.
* `TotalChern.newton_identity_range` — Newton's identity in the `Finset.range`
  form, unconditionally.
-/

namespace GroupApproximation
namespace AlgTop
namespace TotalChern

open Finset (antidiagonal mem_antidiagonal)
open scoped Nat

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The degree-`q` component of the **Chern character** of a total Chern class:
the `q`-th power sum divided by `q!`.  For a split class this is
`(∑ᵢ aᵢ^q) / q!` in the Chern roots, the classical formula. -/
def chernChar (c : TotalChern A) (q : ℕ) : A := ((q ! : ℚ)⁻¹) • c.powerSum q

theorem factorial_mul_chernChar (c : TotalChern A) (q : ℕ) :
    ((q ! : ℕ) : A) * c.chernChar q = c.powerSum q := by
  have hne : ((q ! : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos q).ne'
  have hcast : ((q ! : ℕ) : A) = algebraMap ℚ A ((q ! : ℕ) : ℚ) := (map_natCast _ _).symm
  rw [chernChar, Algebra.smul_def, hcast, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hne,
    map_one, one_mul]

/-- **Newton's identity**, in the `Finset.range` form used by
the parity chain states it, for every total Chern class over a
`ℚ`-algebra — including a virtual one.  No splitting principle and no topology:
it is the coefficientwise form of `c · N(c) = X c'`. -/
theorem newton_identity_range (c : TotalChern A) (q : ℕ) (hq : 0 < q) :
    (∑ i ∈ Finset.range q,
        (-1 : A) ^ i * c.chernClass i * (((q - i)! : ℕ) : A) * c.chernChar (q - i))
      + (-1 : A) ^ q * (q : A) * c.chernClass q = 0 := by
  have hmain := c.natCast_mul_chernClass q
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => c.chernClass i * ((-1 : A) ^ (j + 1) * c.powerSum j)) q,
    Finset.sum_range_succ] at hmain
  simp only [Nat.sub_self, powerSum_zero, mul_zero, add_zero] at hmain
  have hsum : (∑ i ∈ Finset.range q,
      (-1 : A) ^ i * c.chernClass i * (((q - i)! : ℕ) : A) * c.chernChar (q - i))
      = ∑ i ∈ Finset.range q, (-1 : A) ^ i * c.chernClass i * c.powerSum (q - i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, factorial_mul_chernChar]
  have hlast : (-1 : A) ^ q * (q : A) * c.chernClass q
      = (-1 : A) ^ q * ∑ k ∈ Finset.range q,
          c.chernClass k * ((-1 : A) ^ ((q - k) + 1) * c.powerSum (q - k)) := by
    rw [mul_assoc, hmain]
  rw [hsum, hlast, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hiq : i < q := Finset.mem_range.mp hi
  have hsign : (-1 : A) ^ q * (-1 : A) ^ ((q - i) + 1) = -((-1 : A) ^ i) := by
    have hexp : q + ((q - i) + 1) = 2 * (q - i) + (i + 1) := by omega
    rw [← pow_add, hexp, pow_add, pow_mul, neg_one_sq, one_pow, one_mul, pow_succ]
    ring
  linear_combination (c.chernClass i * c.powerSum (q - i)) * hsign

end

end TotalChern
end AlgTop
end GroupApproximation
