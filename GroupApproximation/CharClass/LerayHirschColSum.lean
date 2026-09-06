import GroupApproximation.CharClass.LerayHirschColRead

/-!
# A column's tower has the column's sum

The last step before uniqueness: the tower built from a column has, term by term,
the column's own summands.  Below the tower's length that is the read-back; above
it both sides vanish, the tower's because it has no coefficient there and the
column's because the side condition kills it.

That the two vanishings coincide is the whole reason the reconciliation closes in
this direction, and it is where the side condition earns its place in
`HasFreeTuple`.

## Main declarations

* `towerSumFun_colTower` — **term by term, the tower's sum is the column's**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **Term by term, the tower built from a column has the column's summands.** -/
theorem towerSumFun_colTower (hd : 1 ≤ d + 1) (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod2 (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    (hm : m < 2)
    (hside : ∀ i : Fin (d + 2), m + 2 * k < 2 * (i : ℕ) → a i = 0)
    {i : ℕ} (hi : i < d + 2) :
    towerSumFun U d hd m k (colTower U d m k a) i
      = lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
          (m + 2 * k) i (a ⟨i, hi⟩) := by
  by_cases hik : i ≤ k
  · rw [towerSumFun, towerCoeff_colTower U d m k a hik hi]
  · rw [towerSumFun, towerCoeff_of_gt U m k _ hik,
      hside ⟨i, hi⟩ (by show m + 2 * k < 2 * i; omega)]

/-- **Uniqueness of the column.**  A column summing to zero is zero, at every degree
and every rank: present it as a tower, apply `cc-cohom-api`'s freeness, and read the
coefficients back. -/
theorem freeTuple_unique (hd : 1 ≤ d + 1) (n : ℕ)
    (a : (i : Fin (d + 2)) → Hmod2 (TopCat.of U) (n - 2 * (i : ℕ)))
    (hside : ∀ i : Fin (d + 2), n < 2 * (i : ℕ) → a i = 0)
    (hzero : ∑ i : Fin (d + 2),
        lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 (cpGen (d + 1) hd))
          n (i : ℕ) (a i) = 0) :
    ∀ i : Fin (d + 2), a i = 0 := by
  obtain ⟨m, k, hm, hN⟩ : ∃ m k, m < 2 ∧ m + 2 * k = n :=
    ⟨n % 2, n / 2, Nat.mod_lt _ (by omega), by omega⟩
  subst hN
  have htow : KnCP.peelTower U d hd m (colTower U d m k a) k = 0 := by
    rw [peelTower_eq_range_sum,
      sum_towerSumFun_range_le U d hd m k _ (k + 1) (max (k + 1) (d + 2)) (le_max_left _ _)
        (fun i _ _ => towerSumFun_eq_zero_of_gt U d hd m k _ hm (by omega)),
      ← sum_towerSumFun_range_le U d hd m k _ (d + 2) (max (k + 1) (d + 2))
        (le_max_right _ _)
        (fun i _ _ => towerSumFun_eq_zero_of_rank U d hd m k _ (by omega)),
      ← Fin.sum_univ_eq_sum_range
        (fun i => towerSumFun U d hd m k (colTower U d m k a) i) (d + 2),
      Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        towerSumFun_colTower U d hd m k a hm hside i.2)]
    exact hzero
  have hfree := KnCP.peelFreeAt d U hd m k (colTower U d m k a) htow
  intro i
  by_cases hik : (i : ℕ) ≤ k
  · have h1 := hfree (k - (i : ℕ)) (by omega) (by omega)
    rw [colTower_of U d m k a ⟨by omega, by omega⟩] at h1
    have h2 : a (⟨k - (k - (i : ℕ)), by omega⟩ : Fin (d + 2)) = 0 :=
      (cohCast_eq_zero_iff _ _).mp h1
    have hfin : (⟨k - (k - (i : ℕ)), by omega⟩ : Fin (d + 2)) = i := by
      apply Fin.ext
      show k - (k - (i : ℕ)) = (i : ℕ)
      omega
    have h3 := col_index_congr U d m k a hfin
      (show m + 2 * k - 2 * ((⟨k - (k - (i : ℕ)), by omega⟩ : Fin (d + 2)) : ℕ)
        = m + 2 * k - 2 * (i : ℕ) by
        show m + 2 * k - 2 * (k - (k - (i : ℕ))) = m + 2 * k - 2 * (i : ℕ)
        omega) rfl
    rw [h2, cohCast_zero, cohCast_rfl] at h3
    exact h3.symm
  · exact hside i (by omega)

end

end LH
end CharClass
end GroupApproximation
