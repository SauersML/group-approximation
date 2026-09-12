import GroupApproximation.CharClass.LerayHirschTowerSum
import GroupApproximation.CharClass.CohomologyChartTowerOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The tower, expanded into column terms, over any coefficients

The coefficient-generic form of `CharClass/LerayHirschTowerSum.lean`, against an arbitrary fibre
class `h` of `ℂP^{d+1}` rather than the mod-2 generator.  Nothing in the expansion uses a property
of the coefficients: the three shift lemmas hold over any commutative ring, and the tower identity
over a field only because `KnCP.peelTowerOf` is stated there.

The shift is the right-handed one: cupping a column term with the class on the right raises the
index by one with no transport on the ambient degree.  The summation index is `Fin (k+1)`, which
carries the bound `i ≤ k` the reflected index `k - i` needs for its coefficient's degree to
elaborate.

## Main declarations

* `LH.lhTerm_index_congrOf`, `LH.sum_cup_rightOf`, `LH.lhTerm_succ_rightOf` — over any ring.
* `LH.peelTower_eq_sumOf` — **the tower is the column sum** at the reflected index, over a field.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

section Shift

variable {K : Type} [CommRing K] {X P : TopCat.{0}}

/-- Changing a column term's index, transporting the coefficient. -/
theorem lhTerm_index_congrOf (π : P ⟶ X) (ξ : Hmod K P 2) (n : ℕ) {j j' : ℕ} (h : j = j')
    (c : Hmod K X (n - 2 * j)) :
    lhTerm π ξ n j c = lhTerm π ξ n j' (cohCast (by rw [h]) c) := by
  subst h
  rw [cohCast_self]

/-- Cupping a finite sum on the right, distributed. -/
theorem sum_cup_rightOf {ι : Type} [Fintype ι] {n : ℕ} (f : ι → Hmod K P n)
    (e : Hmod K P 2) : cup (∑ i, f i) e = ∑ i, cup (f i) e :=
  map_sum (cupRightE e n) f Finset.univ

/-- **The cast-free shift.**  Cupping with the class on the right raises the index by one, and the
ambient degree needs no transport. -/
theorem lhTerm_succ_rightOf (π : P ⟶ X) (ξ : Hmod K P 2) (m j : ℕ)
    (a : Hmod K X (m - 2 * j)) :
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

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **The tower is the column sum**, over a field and against any fibre class.  The tower's
`i`-th coefficient is the one for the power `k - i`, so it sits at index `k - i` of the column. -/
theorem peelTower_eq_sumOf (h : Hmod K (CPtop (d + 1)) 2) (m : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) (k : ℕ) :
    KnCP.peelTowerOf K U d h m a k
      = ∑ i : Fin (k + 1),
          lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h)
            (m + 2 * k) (k - (i : ℕ))
            (cohCast (by have := i.2; omega :
              m + 2 * (i : ℕ) = m + 2 * k - 2 * (k - (i : ℕ))) (a i)) := by
  induction k with
  | zero =>
    rw [Fin.sum_univ_one]
    show KnCP.peelTowerOf K U d h m a 0 = _
    simp only [KnCP.peelTowerOf, Fin.val_zero, Nat.sub_zero]
    rw [lhTerm_zero_index, pull_cohCast, cohCast_self]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    show pull (KnCP.cpPrU U d) (m + 2 * (k + 1)) (a (k + 1))
        + cup (KnCP.peelTowerOf K U d h m a k) (pull (KnCP.cpPrCP U d) 2 h) = _
    rw [ih, sum_cup_rightOf]
    have hterm : ∀ i : Fin (k + 1),
        cup (lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h)
              (m + 2 * k) (k - (i : ℕ))
              (cohCast (by have := i.2; omega :
                m + 2 * (i : ℕ) = m + 2 * k - 2 * (k - (i : ℕ))) (a i)))
            (pull (KnCP.cpPrCP U d) 2 h)
          = lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h)
              (m + 2 * (k + 1)) (k + 1 - (i : ℕ))
              (cohCast (by have := i.2; omega :
                m + 2 * (i : ℕ)
                  = m + 2 * (k + 1) - 2 * (k + 1 - (i : ℕ))) (a i)) := by
      intro i
      have hi : (i : ℕ) ≤ k := by have := i.2; omega
      show cup (lhTerm _ _ (m + 2 * k) (k - (i : ℕ)) _) _ = _
      rw [← lhTerm_succ_rightOf,
        lhTerm_index_congrOf _ _ _ (show k - (i : ℕ) + 1 = k + 1 - (i : ℕ) by omega)]
      congr 1
      simp only [cohCast_cohCast]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i)]
    have hlast : lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h)
        (m + 2 * (k + 1)) (k + 1 - ((Fin.last (k + 1) : Fin (k + 2)) : ℕ))
        (cohCast (by simp only [Fin.val_last]; omega :
          m + 2 * ((Fin.last (k + 1) : Fin (k + 2)) : ℕ)
          = m + 2 * (k + 1) - 2 * (k + 1 - ((Fin.last (k + 1) : Fin (k + 2)) : ℕ)))
          (a (Fin.last (k + 1))))
        = pull (KnCP.cpPrU U d) (m + 2 * (k + 1)) (a (k + 1)) := by
      show lhTerm _ _ (m + 2 * (k + 1)) (k + 1 - (k + 1)) _ = _
      rw [lhTerm_index_congrOf _ _ _ (show k + 1 - (k + 1) = 0 by omega),
        lhTerm_zero_index]
      simp
    conv_rhs => rw [hlast]
    exact add_comm _ _

end

end LH

/-! Audited on every build. -/

#audit_axioms LH.lhTerm_succ_rightOf
#audit_axioms LH.peelTower_eq_sumOf

end CharClass
end GroupApproximation
