import GroupApproximation.CharClass.LerayHirschTowerBridge
import GroupApproximation.CharClass.CohomologyChartTower

/-!
# The tower, expanded into column terms

`cc-cohom-api`'s `peelTower` is a Horner nesting; the ladder consumes a sum of
column terms.  Expanding one into the other is this file, by induction on the
tower's length.

Two things make it go through.

The shift used here is the **right-handed** one: cupping a column term with the
class on the right raises the index by one and needs no transport on the ambient
degree at all, because `m + 2` is what `cup _ ξ` already produces.  The left-handed
shift in `LerayHirschShiftTerm` needs a commutation and a cast.  This is the same
observation `cc-cohom-api` made about their tower, arriving from the other side.

The summation index is `Fin (k+1)` rather than `Finset.range (k+1)`.  The reflected
index `k - i` is truncated subtraction, so the cast identifying the coefficient's
degree holds only under `i ≤ k`, and a `Fin` carries that bound in the binder where
a `range` does not.  With a `range` the summand fails to *elaborate*, not to be
provable.

## Main declarations

* `lhTerm_succ_right` — the cast-free shift.
* `lhTerm_index_congr` — changing the index, transporting the coefficient.
* `peelTower_eq_sum` — **the tower is the column sum** at the reflected index.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

section Shift

variable {X P : TopCat.{0}}

/-- Changing a column term's index, transporting the coefficient. -/
theorem lhTerm_index_congr (π : P ⟶ X) (ξ : Hmod2 P 2) (n : ℕ) {j j' : ℕ} (h : j = j')
    (c : Hmod2 X (n - 2 * j)) :
    lhTerm π ξ n j c = lhTerm π ξ n j' (cohCast (by rw [h]) c) := by
  subst h
  rw [cohCast_self]

/-- Cupping a finite sum on the right, distributed. -/
theorem sum_cup_right {ι : Type} [Fintype ι] {n : ℕ} (f : ι → Hmod2 P n)
    (e : Hmod2 P 2) : cup (∑ i, f i) e = ∑ i, cup (f i) e :=
  map_sum (cupRightE e n) f Finset.univ

/-- **The cast-free shift.**  Cupping with the class on the right raises the index by
one, and the ambient degree needs no transport: `cup _ ξ` already lands in `m + 2`. -/
theorem lhTerm_succ_right (π : P ⟶ X) (ξ : Hmod2 P 2) (m j : ℕ)
    (a : Hmod2 X (m - 2 * j)) :
    lhTerm π ξ (m + 2) (j + 1)
        (cohCast (by omega : m - 2 * j = m + 2 - 2 * (j + 1)) a)
      = cup (lhTerm π ξ m j a) ξ := by
  by_cases h : 2 * j ≤ m
  · rw [lhTerm_of_le π ξ h a,
      lhTerm_of_le π ξ (show 2 * (j + 1) ≤ m + 2 by omega)
        (cohCast (by omega : m - 2 * j = m + 2 - 2 * (j + 1)) a),
      pull_cohCast, cup_cohCast_left, cup_cohCast_left, cohCast_cohCast, cupPowE_succ,
      ← cup_assoc]
    simp only [cohCast_cohCast]
  · rw [lhTerm_of_gt π ξ h a,
      lhTerm_of_gt π ξ (show ¬ 2 * (j + 1) ≤ m + 2 by omega)
        (cohCast (by omega : m - 2 * j = m + 2 - 2 * (j + 1)) a),
      zero_cup]

end Shift

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **The tower is the column sum.**  The tower's `i`-th coefficient is the one for
the power `k - i`, so it sits at index `k - i` of the column. -/
theorem peelTower_eq_sum (hd : 1 ≤ d + 1) (m : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) (k : ℕ) :
    KnCP.peelTower U d hd m a k
      = ∑ i : Fin (k + 1),
          lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
            (m + 2 * k) (k - (i : ℕ))
            (cohCast (by have := i.2; omega :
              m + 2 * (i : ℕ) = m + 2 * k - 2 * (k - (i : ℕ))) (a i)) := by
  induction k with
  | zero =>
    rw [Fin.sum_univ_one]
    show KnCP.peelTower U d hd m a 0 = _
    simp only [KnCP.peelTower, Fin.val_zero, Nat.sub_zero]
    rw [lhTerm_zero_index, pull_cohCast, cohCast_self]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    show pull (KnCP.cpPrU U d) (m + 2 * (k + 1)) (a (k + 1))
        + cup (KnCP.peelTower U d hd m a k)
            (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd)) = _
    rw [ih, sum_cup_right]
    have hterm : ∀ i : Fin (k + 1),
        cup (lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
              (m + 2 * k) (k - (i : ℕ))
              (cohCast (by have := i.2; omega :
                m + 2 * (i : ℕ) = m + 2 * k - 2 * (k - (i : ℕ))) (a i)))
            (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
          = lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
              (m + 2 * (k + 1)) (k + 1 - (i : ℕ))
              (cohCast (by have := i.2; omega :
                m + 2 * (i : ℕ)
                  = m + 2 * (k + 1) - 2 * (k + 1 - (i : ℕ))) (a i)) := by
      intro i
      have hi : (i : ℕ) ≤ k := by have := i.2; omega
      show cup (lhTerm _ _ (m + 2 * k) (k - (i : ℕ)) _) _ = _
      rw [← lhTerm_succ_right,
        lhTerm_index_congr _ _ _ (show k - (i : ℕ) + 1 = k + 1 - (i : ℕ) by omega)]
      congr 1
      simp only [cohCast_cohCast]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i)]
    have hlast : lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
        (m + 2 * (k + 1)) (k + 1 - ((Fin.last (k + 1) : Fin (k + 2)) : ℕ))
        (cohCast (by simp only [Fin.val_last]; omega :
          m + 2 * ((Fin.last (k + 1) : Fin (k + 2)) : ℕ)
          = m + 2 * (k + 1) - 2 * (k + 1 - ((Fin.last (k + 1) : Fin (k + 2)) : ℕ)))
          (a (Fin.last (k + 1))))
        = pull (KnCP.cpPrU U d) (m + 2 * (k + 1)) (a (k + 1)) := by
      show lhTerm _ _ (m + 2 * (k + 1)) (k + 1 - (k + 1)) _ = _
      rw [lhTerm_index_congr _ _ _ (show k + 1 - (k + 1) = 0 by omega),
        lhTerm_zero_index]
      simp
    conv_rhs => rw [hlast]
    exact add_comm _ _

end

end LH
end CharClass
end GroupApproximation
