import GroupApproximation.CharClass.LerayHirschTowerSum
import GroupApproximation.CharClass.ProjectiveSpaceRing

/-!
# Column terms above the rank vanish

The ladder's spanning half carries a loose summation range, and the freeness half
comes from a tower whose length is set by the degree rather than by the rank.  Both
therefore produce terms whose power exceeds the fibre's dimension, and both are
reconciled with the column by the observation that those terms are zero.

That is the one place the ring of `ℂP^r` is used in the ladder, and it is used only
through `cupPowE_eq_zero_of_gt`: a power above the dimension lands in a group that
has already vanished.

## Main declarations

* `cupPowE_pull_cpGen_eq_zero` — the powers of the pulled-back generator die.
* `lhTerm_eq_zero_of_rank` — **so do the column terms above the rank**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The powers of the pulled-back generator vanish above the fibre's dimension. -/
theorem cupPowE_pull_cpGen_eq_zero (hd : 1 ≤ d + 1) {i : ℕ} (hi : d + 1 < i) :
    cupPowE (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd)) i = 0 := by
  rw [← pull_cupPowE, cupPowE_eq_zero_of_gt (cpGen (d + 1) hd) (d + 1)
    (hasCPCohomology_CP (d + 1)) hi, pull_zero]

/-- **Column terms above the rank vanish.**  The coefficient is irrelevant: the power
it multiplies is already zero. -/
theorem lhTerm_eq_zero_of_rank (hd : 1 ≤ d + 1) (n : ℕ) {i : ℕ} (hi : d + 1 < i)
    (c : Hmod2 (TopCat.of U) (n - 2 * i)) :
    lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd)) n i c = 0 := by
  by_cases h : 2 * i ≤ n
  · rw [lhTerm_of_le _ _ h c, cupPowE_pull_cpGen_eq_zero U d hd hi, cup_zero, cohCast_zero]
  · rw [lhTerm_of_gt _ _ h c]

end

end LH
end CharClass
end GroupApproximation
