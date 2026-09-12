import GroupApproximation.CharClass.LerayHirschFreeTupleOf
import GroupApproximation.CharClass.CohomologyChartFreenessOf

/-!
# A column's tower has the column's sum, and uniqueness of the column, over a field

The coefficient-generic forms of `LerayHirschColTower`, `LerayHirschColRead` and
`LerayHirschColSum`: a column is read as a tower, the tower's column terms are the column's own,
and a column summing to zero is zero by the freeness of the tower (`KnCP.peelFreeAtOf`).

## Main declarations

* `LH.colTowerOf`, `LH.colTower_ofOf`, `LH.colTower_of_notOf`.
* `LH.col_index_congrOf`, `LH.towerCoeff_colTowerOf`, `LH.towerSumFun_colTowerOf`.
* `LH.freeTuple_uniqueOf` — **uniqueness of the column**, over the ring input.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **A column, read as a tower.** -/
def colTowerOf (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod K (TopCat.of U) (m + 2 * k - 2 * (i : ℕ))) :
    (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j) :=
  fun j => if hj : j ≤ k ∧ k - j < d + 2 then
      cohCast (show m + 2 * k - 2 * ((⟨k - j, hj.2⟩ : Fin (d + 2)) : ℕ) = m + 2 * j by
        have := hj.1
        show m + 2 * k - 2 * (k - j) = m + 2 * j
        omega) (a ⟨k - j, hj.2⟩)
    else 0

theorem colTower_ofOf (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod K (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    {j : ℕ} (hj : j ≤ k ∧ k - j < d + 2) :
    colTowerOf K U d m k a j
      = cohCast (show m + 2 * k - 2 * ((⟨k - j, hj.2⟩ : Fin (d + 2)) : ℕ) = m + 2 * j by
          have := hj.1
          show m + 2 * k - 2 * (k - j) = m + 2 * j
          omega) (a ⟨k - j, hj.2⟩) := dif_pos hj

theorem colTower_of_notOf (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod K (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    {j : ℕ} (hj : ¬ (j ≤ k ∧ k - j < d + 2)) : colTowerOf K U d m k a j = 0 := dif_neg hj

/-- Transporting a column coefficient along an equality of its index. -/
theorem col_index_congrOf (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod K (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    {i j : Fin (d + 2)} (hij : i = j) {D : ℕ}
    (hD₁ : m + 2 * k - 2 * (i : ℕ) = D) (hD₂ : m + 2 * k - 2 * (j : ℕ) = D) :
    cohCast hD₁ (a i) = cohCast hD₂ (a j) := by
  subst hij
  rfl

/-- **Reading the tower back gives the column.** -/
theorem towerCoeff_colTowerOf (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod K (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    {i : ℕ} (hik : i ≤ k) (hid : i < d + 2) :
    towerCoeffOf K U m k (colTowerOf K U d m k a) i = a ⟨i, hid⟩ := by
  have hj : k - i ≤ k := by omega
  have hjd : k - (k - i) < d + 2 := by omega
  rw [towerCoeff_of_leOf K U m k _ hik, colTower_ofOf K U d m k a ⟨hj, hjd⟩]
  have hfin : (⟨k - (k - i), hjd⟩ : Fin (d + 2)) = ⟨i, hid⟩ := by
    apply Fin.ext
    show k - (k - i) = i
    omega
  rw [cohCast_cohCast]
  exact (col_index_congrOf K U d m k a hfin _ rfl).trans (cohCast_rfl _)

/-- **Term by term, the tower built from a column has the column's summands.** -/
theorem towerSumFun_colTowerOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (a : (i : Fin (d + 2)) → Hmod K (TopCat.of U) (m + 2 * k - 2 * (i : ℕ)))
    (hm : m < 2)
    (hside : ∀ i : Fin (d + 2), m + 2 * k < 2 * (i : ℕ) → a i = 0)
    {i : ℕ} (hi : i < d + 2) :
    towerSumFunOf K U d h m k (colTowerOf K U d m k a) i
      = lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h)
          (m + 2 * k) i (a ⟨i, hi⟩) := by
  by_cases hik : i ≤ k
  · rw [towerSumFunOf, towerCoeff_colTowerOf K U d m k a hik hi]
  · rw [towerSumFunOf, towerCoeff_of_gtOf K U m k _ hik,
      hside ⟨i, hi⟩ (by show m + 2 * k < 2 * i; omega)]

set_option maxHeartbeats 1000000 in
/-- **Uniqueness of the column over `K`**, over the ring input: present it as a tower, apply the
freeness of the tower, and read the coefficients back. -/
theorem freeTuple_uniqueOf (hring : KnCP.CPRingOf K) (h : Hmod K (CPtop (d + 1)) 2)
    (h0 : h ≠ 0) (n : ℕ)
    (a : (i : Fin (d + 2)) → Hmod K (TopCat.of U) (n - 2 * (i : ℕ)))
    (hside : ∀ i : Fin (d + 2), n < 2 * (i : ℕ) → a i = 0)
    (hzero : ∑ i : Fin (d + 2),
        lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h) n (i : ℕ) (a i) = 0) :
    ∀ i : Fin (d + 2), a i = 0 := by
  obtain ⟨m, k, hm, hN⟩ : ∃ m k, m < 2 ∧ m + 2 * k = n :=
    ⟨n % 2, n / 2, Nat.mod_lt _ (by omega), by omega⟩
  subst hN
  have htow : KnCP.peelTowerOf K U d h m (colTowerOf K U d m k a) k = 0 := by
    rw [peelTower_eq_range_sumOf,
      sum_towerSumFun_range_leOf K U d h m k _ (k + 1) (max (k + 1) (d + 2)) (le_max_left _ _)
        (fun i _ _ => towerSumFun_eq_zero_of_gtOf K U d h m k _ hm (by omega)),
      ← sum_towerSumFun_range_leOf K U d h m k _ (d + 2) (max (k + 1) (d + 2))
        (le_max_right _ _)
        (fun i _ _ => towerSumFun_eq_zero_of_rankOf K U d h m k _ (by omega)),
      ← Fin.sum_univ_eq_sum_range
        (fun i => towerSumFunOf K U d h m k (colTowerOf K U d m k a) i) (d + 2),
      Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
        towerSumFun_colTowerOf K U d h m k a hm hside i.2)]
    exact hzero
  have hfree := KnCP.peelFreeAtOf K hring d U h h0 m k (colTowerOf K U d m k a) htow
  intro i
  by_cases hik : (i : ℕ) ≤ k
  · have h1 := hfree (k - (i : ℕ)) (by omega) (by omega)
    rw [colTower_ofOf K U d m k a ⟨by omega, by omega⟩] at h1
    have h2 : a (⟨k - (k - (i : ℕ)), by omega⟩ : Fin (d + 2)) = 0 :=
      (cohCast_eq_zero_iff _ _).mp h1
    have hfin : (⟨k - (k - (i : ℕ)), by omega⟩ : Fin (d + 2)) = i := by
      apply Fin.ext
      show k - (k - (i : ℕ)) = (i : ℕ)
      omega
    have h3 := col_index_congrOf K U d m k a hfin
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
