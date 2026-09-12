import GroupApproximation.CharClass.LerayHirschFreeTupleExists

/-!
# Reading the tower's coefficients at the reflected index

`towerCoeff` reads the tower's `j`-th coefficient at column index `k - j`.  The
assembly needs the other direction: what sits at column index `k - i` is the
tower's `i`-th coefficient.  That is a reflection identity, and it is stated here
on its own because the index `k - (k - i)` reducing to `i` is a *dependent*
rewrite: the tower's coefficient type depends on its index, so the step cannot be
done by `rw` at the point of use.

## Main declarations

* `towerCoeff_rev` — the reflected reading.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- Transporting a tower coefficient along an equality of its index.  Both sides
land in the same degree, so `subst` and proof irrelevance close it; this is the step
that cannot be done by `rw`, because the coefficient's type moves with the index. -/
theorem tower_index_congr (m : ℕ) (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    {i j D : ℕ} (h : i = j) (hD₁ : m + 2 * i = D) (hD₂ : m + 2 * j = D) :
    cohCast hD₁ (t i) = cohCast hD₂ (t j) := by
  subst h
  rfl

/-- **The reflected reading.**  At column index `k - i` sits the tower's `i`-th
coefficient. -/
theorem towerCoeff_rev (m k : ℕ) (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    {i : ℕ} (hi : i ≤ k) :
    towerCoeff U m k t (k - i)
      = cohCast (by omega : m + 2 * i = m + 2 * k - 2 * (k - i)) (t i) := by
  rw [towerCoeff_of_le U m k t (show k - i ≤ k by omega)]
  exact tower_index_congr U m t (by omega : k - (k - i) = i) _ _

end

end LH
end CharClass
end GroupApproximation
