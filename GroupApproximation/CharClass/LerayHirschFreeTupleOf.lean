import GroupApproximation.CharClass.LerayHirschTowerSumOf
import GroupApproximation.CharClass.LerayHirschFreeExists
import GroupApproximation.CharClass.CohomologyChartTowerTopOf
import GroupApproximation.Meta.AxiomGuard

/-!
# Every class is a column of length the rank, over a field

The coefficient-generic forms of `LerayHirschFreeTuple`, `LerayHirschFreeTupleExists`,
`LerayHirschRankVanish`, `LerayHirschTowerRev` and `LerayHirschFreeExists`, against an arbitrary
nonzero fibre class: the tower's length is set by the degree and the column's by the rank, and the
two are reconciled through a common range where the extra terms on each side vanish, above the
length because twice the index passes the degree and above the rank because the power passes the
fibre's dimension.

## Main declarations

* `LH.sum_lhTerm_range_leOf`, `LH.towerCoeffOf`, `LH.towerSumFunOf`.
* `LH.lhTerm_eq_zero_of_rankOf` — column terms above the rank vanish.
* `LH.towerCoeff_revOf`, `LH.peelTower_eq_range_sumOf`.
* `LH.exists_freeTupleOf` — **every class is a column**, over the ring input.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

section Range

variable {K : Type} [CommRing K] {X P : TopCat.{0}}

/-- Extending a range of column terms over indices where they vanish, over any ring. -/
theorem sum_lhTerm_range_leOf (π : P ⟶ X) (ξ : Hmod K P 2) (n : ℕ)
    (A : (i : ℕ) → Hmod K X (n - 2 * i)) (N M : ℕ) (hNM : N ≤ M)
    (hvan : ∀ i, N ≤ i → i < M → lhTerm π ξ n i (A i) = 0) :
    ∑ i ∈ Finset.range N, lhTerm π ξ n i (A i)
      = ∑ i ∈ Finset.range M, lhTerm π ξ n i (A i) := by
  refine Finset.sum_subset
    (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hNM)) ?_
  intro i hi hni
  simp only [Finset.mem_range, Nat.not_lt] at hni
  exact hvan i hni (Finset.mem_range.mp hi)

end Range

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-- The tower's coefficients, read at the column's index. -/
def towerCoeffOf (m k : ℕ) (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    (i : ℕ) → Hmod K (TopCat.of U) (m + 2 * k - 2 * i) :=
  fun i => if hi : i ≤ k then cohCast (by omega) (t (k - i)) else 0

theorem towerCoeff_of_leOf (m k : ℕ) (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    {i : ℕ} (hi : i ≤ k) :
    towerCoeffOf K U m k t i
      = cohCast (by omega : m + 2 * (k - i) = m + 2 * k - 2 * i) (t (k - i)) := dif_pos hi

theorem towerCoeff_of_gtOf (m k : ℕ) (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    {i : ℕ} (hi : ¬ i ≤ k) : towerCoeffOf K U m k t i = 0 := dif_neg hi

/-- The column terms of the tower's coefficients, as a total function of the index. -/
def towerSumFunOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) (i : ℕ) :
    Hmod K (KnCP.cpProdTop U d) (m + 2 * k) :=
  lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h) (m + 2 * k) i (towerCoeffOf K U m k t i)

/-- Above the tower's length the terms vanish. -/
theorem towerSumFun_eq_zero_of_gtOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) (hm : m < 2) {i : ℕ} (hi : k < i) :
    towerSumFunOf K U d h m k t i = 0 :=
  lhTerm_of_gt _ _ (by omega) _

/-- **Column terms above the rank vanish**, over `K`. -/
theorem lhTerm_eq_zero_of_rankOf (h : Hmod K (CPtop (d + 1)) 2) (n : ℕ) {i : ℕ}
    (hi : d + 1 < i) (c : Hmod K (TopCat.of U) (n - 2 * i)) :
    lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h) n i c = 0 := by
  by_cases hle : 2 * i ≤ n
  · rw [lhTerm_of_le _ _ hle c, KnCP.cupPowE_pull_eq_zeroOf K U d h i hi, cup_zero,
      cohCast_zero]
  · rw [lhTerm_of_gt _ _ hle c]

/-- Above the rank the terms vanish. -/
theorem towerSumFun_eq_zero_of_rankOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) {i : ℕ} (hi : d + 1 < i) :
    towerSumFunOf K U d h m k t i = 0 :=
  lhTerm_eq_zero_of_rankOf K U d h (m + 2 * k) hi _

/-- Transporting a tower coefficient along an equality of its index. -/
theorem tower_index_congrOf (m : ℕ) (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    {i j D : ℕ} (hij : i = j) (hD₁ : m + 2 * i = D) (hD₂ : m + 2 * j = D) :
    cohCast hD₁ (t i) = cohCast hD₂ (t j) := by
  subst hij
  rfl

/-- **The reflected reading.**  At column index `k - i` sits the tower's `i`-th coefficient. -/
theorem towerCoeff_revOf (m k : ℕ) (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    {i : ℕ} (hi : i ≤ k) :
    towerCoeffOf K U m k t (k - i)
      = cohCast (by omega : m + 2 * i = m + 2 * k - 2 * (k - i)) (t i) := by
  rw [towerCoeff_of_leOf K U m k t (show k - i ≤ k by omega)]
  exact tower_index_congrOf K U m t (by omega : k - (k - i) = i) _ _

/-- The tower, as a column sum over a range. -/
theorem peelTower_eq_range_sumOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    KnCP.peelTowerOf K U d h m t k
      = ∑ i ∈ Finset.range (k + 1), towerSumFunOf K U d h m k t i := by
  rw [peelTower_eq_sumOf]
  rw [show (∑ i : Fin (k + 1),
        lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h)
          (m + 2 * k) (k - (i : ℕ))
          (cohCast (by have := i.2; omega :
            m + 2 * (i : ℕ) = m + 2 * k - 2 * (k - (i : ℕ))) (t i)))
      = ∑ i : Fin (k + 1), towerSumFunOf K U d h m k t (k - (i : ℕ)) from
    Finset.sum_congr rfl fun i _ => by
      rw [towerSumFunOf, towerCoeff_revOf K U m k t (by have := i.2; omega : (i : ℕ) ≤ k)]]
  rw [Fin.sum_univ_eq_sum_range (fun i => towerSumFunOf K U d h m k t (k - i)) (k + 1)]
  exact Finset.sum_range_reflect (fun i => towerSumFunOf K U d h m k t i) (k + 1)

/-- Extending the range of a tower's column sum over vanishing terms. -/
theorem sum_towerSumFun_range_leOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (t : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) (N M : ℕ) (hNM : N ≤ M)
    (hvan : ∀ i, N ≤ i → i < M → towerSumFunOf K U d h m k t i = 0) :
    ∑ i ∈ Finset.range N, towerSumFunOf K U d h m k t i
      = ∑ i ∈ Finset.range M, towerSumFunOf K U d h m k t i :=
  sum_lhTerm_range_leOf _ _ _ (towerCoeffOf K U m k t) N M hNM hvan

set_option maxHeartbeats 1000000 in
/-- **Every class is a column of length the rank**, over `K`, over the ring input. -/
theorem exists_freeTupleOf (hring : KnCP.CPRingOf K) (h : Hmod K (CPtop (d + 1)) 2)
    (h0 : h ≠ 0) (n : ℕ) (z : Hmod K (KnCP.cpProdTop U d) n) :
    ∃ a : (i : Fin (d + 2)) → Hmod K (TopCat.of U) (n - 2 * (i : ℕ)),
      (∀ i : Fin (d + 2), n < 2 * (i : ℕ) → a i = 0)
        ∧ z = ∑ i : Fin (d + 2),
            lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h) n (i : ℕ) (a i) := by
  obtain ⟨m, k, hm, hN, t, hz⟩ := KnCP.exists_peelTowerOf K U d hring h h0 n z
  subst hN
  refine ⟨fun i => towerCoeffOf K U m k t (i : ℕ),
    fun i hi => towerCoeff_of_gtOf K U m k t (by omega), ?_⟩
  have h1 : z = ∑ i ∈ Finset.range (k + 1), towerSumFunOf K U d h m k t i := by
    rw [hz, cohCast_self, peelTower_eq_range_sumOf]
  have h2 : ∑ i : Fin (d + 2),
      lhTerm (KnCP.cpPrU U d) (pull (KnCP.cpPrCP U d) 2 h)
        (m + 2 * k) (i : ℕ) (towerCoeffOf K U m k t (i : ℕ))
      = ∑ i ∈ Finset.range (d + 2), towerSumFunOf K U d h m k t i :=
    Fin.sum_univ_eq_sum_range (fun i => towerSumFunOf K U d h m k t i) (d + 2)
  rw [h1, h2,
    sum_towerSumFun_range_leOf K U d h m k t (k + 1) (max (k + 1) (d + 2)) (le_max_left _ _)
      (fun i hi _ => towerSumFun_eq_zero_of_gtOf K U d h m k t hm (by omega)),
    sum_towerSumFun_range_leOf K U d h m k t (d + 2) (max (k + 1) (d + 2)) (le_max_right _ _)
      (fun i hi _ => towerSumFun_eq_zero_of_rankOf K U d h m k t (by omega))]

end

end LH

/-! Audited on every build. -/

#audit_axioms LH.lhTerm_eq_zero_of_rankOf
#audit_axioms LH.peelTower_eq_range_sumOf
#audit_axioms LH.exists_freeTupleOf

end CharClass
end GroupApproximation
