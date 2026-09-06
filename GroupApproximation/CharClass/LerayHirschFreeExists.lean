import GroupApproximation.CharClass.LerayHirschTowerRev
import GroupApproximation.CharClass.LerayHirschTowerSum

/-!
# Every class is a column of length the rank

The existence half of the reconciliation.  `exists_peelTower` gives a tower whose
length the degree fixes; the column's length is the rank.  Read the tower's
coefficients at the reflected index, extend both sums to a common range, and the
extra terms on each side vanish for the two independent reasons already proved.

## Main declarations

* `peelTower_eq_range_sum` — the tower as a column sum over its own length.
* `exists_freeTuple` — **every class is a column** of length the rank.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The tower, as a column sum over a range rather than a `Fin`. -/
theorem peelTower_eq_range_sum (hd : 1 ≤ d + 1) (m k : ℕ)
    (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    KnCP.peelTower U d hd m t k
      = ∑ i ∈ Finset.range (k + 1), towerSumFun U d hd m k t i := by
  rw [peelTower_eq_sum]
  rw [show (∑ i : Fin (k + 1),
        lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
          (m + 2 * k) (k - (i : ℕ))
          (cohCast (by have := i.2; omega :
            m + 2 * (i : ℕ) = m + 2 * k - 2 * (k - (i : ℕ))) (t i)))
      = ∑ i : Fin (k + 1), towerSumFun U d hd m k t (k - (i : ℕ)) from
    Finset.sum_congr rfl fun i _ => by
      rw [towerSumFun, towerCoeff_rev U m k t (by have := i.2; omega : (i : ℕ) ≤ k)]]
  rw [Fin.sum_univ_eq_sum_range (fun i => towerSumFun U d hd m k t (k - i)) (k + 1)]
  exact Finset.sum_range_reflect (fun i => towerSumFun U d hd m k t i) (k + 1)

/-- Extending the range of a tower's column sum over vanishing terms. -/
theorem sum_towerSumFun_range_le (hd : 1 ≤ d + 1) (m k : ℕ)
    (t : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) (N M : ℕ) (hNM : N ≤ M)
    (hvan : ∀ i, N ≤ i → i < M → towerSumFun U d hd m k t i = 0) :
    ∑ i ∈ Finset.range N, towerSumFun U d hd m k t i
      = ∑ i ∈ Finset.range M, towerSumFun U d hd m k t i :=
  sum_lhTerm_range_le _ _ _ (towerCoeff U m k t) N M hNM hvan

/-- **Every class is a column of length the rank.**  The tower's length is set by the
degree; the two are reconciled through a common range where each side's extra terms
vanish, above the length because twice the index passes the degree and above the rank
because the power passes the fibre's dimension. -/
theorem exists_freeTuple (hd : 1 ≤ d + 1) (n : ℕ) (z : Hmod2 (KnCP.cpProdTop U d) n) :
    ∃ a : (i : Fin (d + 2)) → Hmod2 (TopCat.of U) (n - 2 * (i : ℕ)),
      (∀ i : Fin (d + 2), n < 2 * (i : ℕ) → a i = 0)
        ∧ z = ∑ i : Fin (d + 2),
            lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
              n (i : ℕ) (a i) := by
  obtain ⟨m, k, hm, hN, t, hz⟩ := KnCP.exists_peelTower U d hd n z
  subst hN
  refine ⟨fun i => towerCoeff U m k t (i : ℕ),
    fun i hi => towerCoeff_of_gt U m k t (by omega), ?_⟩
  have h1 : z = ∑ i ∈ Finset.range (k + 1), towerSumFun U d hd m k t i := by
    rw [hz, cohCast_self, peelTower_eq_range_sum]
  have h2 : ∑ i : Fin (d + 2),
      lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
        (m + 2 * k) (i : ℕ) (towerCoeff U m k t (i : ℕ))
      = ∑ i ∈ Finset.range (d + 2), towerSumFun U d hd m k t i :=
    Fin.sum_univ_eq_sum_range (fun i => towerSumFun U d hd m k t i) (d + 2)
  rw [h1, h2,
    sum_towerSumFun_range_le U d hd m k t (k + 1) (max (k + 1) (d + 2)) (le_max_left _ _)
      (fun i hi _ => towerSumFun_eq_zero_of_gt U d hd m k t hm (by omega)),
    sum_towerSumFun_range_le U d hd m k t (d + 2) (max (k + 1) (d + 2)) (le_max_right _ _)
      (fun i hi _ => towerSumFun_eq_zero_of_rank U d hd m k t (by omega))]

end

end LH
end CharClass
end GroupApproximation
