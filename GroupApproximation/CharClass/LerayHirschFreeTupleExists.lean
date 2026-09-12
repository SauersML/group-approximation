import GroupApproximation.CharClass.LerayHirschFreeTuple
import GroupApproximation.CharClass.LerayHirschTowerSum

/-!
# Every class is a column, at the rank

`exists_peelTower` produces a tower whose length the degree fixes; the column's
length is fixed by the rank.  This is the reconciliation in the existence
direction: read the tower's coefficients at the column's index and extend both
sums to a common range, where the extra terms on each side vanish for the two
different reasons already proved.

## Main declarations

* `towerSumFun` — the column terms of the tower's coefficients, as a total function.
* `exists_freeTuple` — **every class is a column** of length the rank.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The column terms of the tower's coefficients, as a total function of the index. -/
def towerSumFun (hd : 1 ≤ d + 1) (m k : ℕ)
    (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) (i : ℕ) :
    Hmod2 (KnCP.cpProdTop U d) (m + 2 * k) :=
  lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
    (m + 2 * k) i (towerCoeff U m k t i)

/-- Above the tower's length the terms vanish, because twice the index passes the
degree. -/
theorem towerSumFun_eq_zero_of_gt (hd : 1 ≤ d + 1) (m k : ℕ)
    (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) (hm : m < 2) {i : ℕ} (hi : k < i) :
    towerSumFun U d hd m k t i = 0 :=
  lhTerm_of_gt _ _ (by omega) _

/-- Above the rank the terms vanish, because the power has passed the fibre's
dimension. -/
theorem towerSumFun_eq_zero_of_rank (hd : 1 ≤ d + 1) (m k : ℕ)
    (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) {i : ℕ} (hi : d + 1 < i) :
    towerSumFun U d hd m k t i = 0 :=
  lhTerm_eq_zero_of_rank U d hd (m + 2 * k) hi _

end

end LH
end CharClass
end GroupApproximation
