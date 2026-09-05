import GroupApproximation.AlgTop.ChernNewtonIdentity

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
/-!
# Equation (2.7) with no Newton hypothesis

`GroupApproximation.AlgTop.MappingTorusParity.two_dvd_chernClass_of_parity`
takes as its hypothesis `hshift` the conclusion of the manuscript's (2.7),

```text
c_k = (-1)^{k+1} (k-1)! ch_k    for k > 0,
```

valid because the Chern character of the virtual class `δ` is square-zero.  The
usual route to (2.7) assumes Newton's identity and calls it the splitting
principle.  Here it is not assumed: for a total Chern class encoded as a
normalized power series, Newton's identity is a theorem
(`GroupApproximation.AlgTop.TotalChern.newton_identity_range`), proved from the
logarithmic derivative and valid for virtual classes as well as bundles.

So the statement below has **no algebraic hypothesis at all**: only the
square-zero condition on the Chern character, which is what `z² = 0` supplies in
the manuscript.  Its conclusion is `hshift` verbatim, with `ch := chernChar`.

## Main declarations

* `isUnit_natCast_pos` — `(k : A)` is a unit in a `ℚ`-algebra when `k > 0`.
* `TotalChern.chernClass_eq_of_chernChar_sq_zero` — (2.7).
-/

namespace GroupApproximation
namespace AlgTop

open scoped Nat

/-- In a `ℚ`-algebra every positive natural number is a unit.  This is the only
use made of the rational coefficients: Newton's identity determines `k · c_k`,
and `k` has to be divided out. -/
theorem isUnit_natCast_pos {A : Type*} [CommRing A] [Algebra ℚ A] {k : ℕ} (hk : 0 < k) :
    IsUnit ((k : ℕ) : A) := by
  have hcast : ((k : ℕ) : A) = algebraMap ℚ A ((k : ℕ) : ℚ) := (map_natCast _ _).symm
  rw [hcast]
  refine IsUnit.map (algebraMap ℚ A) (isUnit_iff_ne_zero.2 ?_)
  exact_mod_cast hk.ne'

namespace TotalChern

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- **(2.7), unconditionally.**  If the positive-degree components of the Chern
character annihilate one another — which is what `z² = 0` gives for the virtual
class of the mapping torus — then `c_q = (-1)^{q+1} (q-1)! ch_q`.

There is no Newton hypothesis: `newton_identity_range` supplies it. -/
theorem chernClass_eq_of_chernChar_sq_zero (c : TotalChern A)
    (hsq : ∀ i j : ℕ, 0 < i → 0 < j → c.chernChar i * c.chernChar j = 0) :
    ∀ q : ℕ, 0 < q →
      c.chernClass q
        = (-1 : A) ^ (q + 1) * ((((q - 1)! : ℕ) : A) * c.chernChar q) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro hq
    have hnewton := c.newton_identity_range q hq
    have hzero : ∀ i ∈ Finset.range q, i ≠ 0 →
        (-1 : A) ^ i * c.chernClass i * (((q - i)! : ℕ) : A) * c.chernChar (q - i) = 0 := by
      intro i hi hi0
      have hiq : i < q := Finset.mem_range.mp hi
      have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      have hsub : 0 < q - i := by omega
      have hz := hsq i (q - i) hipos hsub
      rw [ih i hiq hipos]
      linear_combination ((-1 : A) ^ i * ((-1 : A) ^ (i + 1) * ((((i - 1)! : ℕ) : A))) *
        ((((q - i)! : ℕ) : A))) * hz
    have hsum : (∑ i ∈ Finset.range q,
        (-1 : A) ^ i * c.chernClass i * (((q - i)! : ℕ) : A) * c.chernChar (q - i))
        = (((q ! : ℕ)) : A) * c.chernChar q := by
      refine (Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hq) hzero).trans ?_
      rw [c.chernClass_zero]
      simp
    rw [hsum] at hnewton
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hfac : (((n + 1)! : ℕ) : A) = ((n + 1 : ℕ) : A) * (((n !) : ℕ) : A) := by
      rw [Nat.factorial_succ, Nat.cast_mul]
    have hpow1 : (-1 : A) ^ (n + 1) = -((-1 : A) ^ n) := by
      rw [pow_succ]; ring
    have hpow2 : (-1 : A) ^ (n + 1 + 1) = (-1 : A) ^ n := by
      rw [pow_succ, pow_succ]; ring
    have hs : ((-1 : A) ^ n) * ((-1 : A) ^ n) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    rw [hfac, hpow1] at hnewton
    rw [hpow2]
    refine (isUnit_natCast_pos (A := A) (k := n + 1) (by omega)).mul_left_cancel ?_
    linear_combination (-((-1 : A) ^ n)) * hnewton
      + (-(((n + 1 : ℕ) : A) * c.chernClass (n + 1))) * hs

end

end TotalChern
end AlgTop
end GroupApproximation
