import GroupApproximation.CharClass.LerayHirschRankVanish
import GroupApproximation.CharClass.LerayHirschColumnPack
import GroupApproximation.CharClass.CohomologyChartFreeness

/-!
# From the tower to the column, in both directions

`cc-cohom-api`'s free-module statement is about towers, whose length the degree
fixes; the ladder's is about columns, whose length the rank fixes.  Neither index
set contains the other, and reconciling them is what this file does.

The reconciliation is not an argument, it is two vanishings.  A term the tower has
and the column lacks carries a power above the rank, and dies by
`lhTerm_eq_zero_of_rank`.  A term the column has and the tower lacks has twice its
index above the degree, and dies by `lhTerm_of_gt`.  So both sums agree with the
sum over the union, and `Finset.sum_subset` does the rest.

## Main declarations

* `sum_lhTerm_range_le` — extending the range over vanishing terms.
* `towerCoeff` — the tower's coefficients read as a column.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

section Range

variable {X P : TopCat.{0}}

/-- Extending a range of column terms over indices where they vanish. -/
theorem sum_lhTerm_range_le (π : P ⟶ X) (ξ : Hmod2 P 2) (n : ℕ)
    (A : (i : ℕ) → Hmod2 X (n - 2 * i)) (N M : ℕ) (hNM : N ≤ M)
    (hvan : ∀ i, N ≤ i → i < M → lhTerm π ξ n i (A i) = 0) :
    ∑ i ∈ Finset.range N, lhTerm π ξ n i (A i)
      = ∑ i ∈ Finset.range M, lhTerm π ξ n i (A i) :=
  by
  refine Finset.sum_subset
    (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hNM)) ?_
  intro i hi hni
  simp only [Finset.mem_range, Nat.not_lt] at hni
  exact hvan i hni (Finset.mem_range.mp hi)

end Range

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The tower's coefficients, read at the column's index: the coefficient of the
`i`-th power is the tower's `(k - i)`-th, and there is none once `i` passes `k`. -/
def towerCoeff (m k : ℕ) (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    (i : ℕ) → Hmod2 (TopCat.of U) (m + 2 * k - 2 * i) :=
  fun i => if h : i ≤ k then cohCast (by omega) (t (k - i)) else 0

theorem towerCoeff_of_le (m k : ℕ) (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    {i : ℕ} (h : i ≤ k) :
    towerCoeff U m k t i = cohCast (by omega : m + 2 * (k - i) = m + 2 * k - 2 * i)
      (t (k - i)) := dif_pos h

theorem towerCoeff_of_gt (m k : ℕ) (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    {i : ℕ} (h : ¬ i ≤ k) : towerCoeff U m k t i = 0 := dif_neg h

end

end LH
end CharClass
end GroupApproximation
