import GroupApproximation.CharClass.CohomologyChartTowerTop

/-!
# Freeness of the peel tower, discharged

The induction is on the **rank**.  Restricting a vanishing tower to the punctured
piece gives the tower at the smaller rank with the same coefficients and the same
base degree, so the inductive hypothesis reaches every coefficient whose power
survives there.  Exactly one index escapes, and `peelTower_top_index_eq_zero_all`
reaches it.

Stating freeness index by index rather than under a global length bound is what
makes the restriction step free of casts: the tower does not have to be reindexed,
because it is literally the same tower.

## Main declarations

* `KnCP.pull_sInclusion_peelTower` — a tower restricts to the tower.
* `KnCP.cpTop_cup_injective_all` — the top class is injective on pullbacks at
  every rank including the lowest, where the hypothesis-free rank-two form applies.
* `KnCP.peelTower_top_index_eq_zero_all` — the escaping index with no rank
  hypothesis.
* `KnCP.peelFreeAt` — **freeness, discharged at every rank**.
* `KnCP.peelFree` — the bounded specialisation.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. Injectivity of the top class at every rank -/

/-- **The top class is injective on pullbacks at every rank**, the lowest
included: there the hypothesis-free rank-two form applies. -/
theorem cpTop_cup_injective_all (m : ℕ) (b : Hmod2 (TopCat.of U) m)
    (h : cup (cpTop U d) (pull (cpPrU U d) m b) = 0) : b = 0 := by
  match d with
  | 0 => exact cpTop_cup_injective_zero U m b h
  | (e + 1) => exact cpTop_cup_injective_closed U (e + 1) (by omega) m b h

set_option maxHeartbeats 1000000 in
/-- The escaping index, with the rank hypothesis removed. -/
theorem peelTower_top_index_eq_zero_all (hd : 1 ≤ d + 1) (m j₀ : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j))
    (hhi : ∀ j, j₀ < j → j ≤ j₀ + (d + 1) → a j = 0)
    (hzero : peelTower U d hd m a (j₀ + (d + 1)) = 0) : a j₀ = 0 := by
  have hcol := peelTower_eq_cup_pow U d hd m j₀ a (d + 1) hhi
  have hz : cup (peelTower U d hd m a j₀)
      (cupPowE (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) (d + 1)) = 0 :=
    (cohCast_eq_zero_iff _ _).mp (hcol.symm.trans hzero)
  rw [cup_peelTower_cupPowE_top U d hd m j₀ a] at hz
  have htop : cup (pull (cpPrU U d) (m + 2 * j₀) (a j₀)) (cpTop U d) = 0 := by
    rw [cpTop_eq_pull_cupPowE U d hd, pull_cupPowE]
    exact hz
  refine cpTop_cup_injective_all U d (m + 2 * j₀) (a j₀) ?_
  rw [cup_comm (cpTop U d) (pull (cpPrU U d) (m + 2 * j₀) (a j₀)), htop, cohCast_zero]

/-! ## 2. The tower's equations at normalised degrees -/

/-- The tower at length zero, with the degree written as `m` rather than
`m + 2 * 0`. -/
theorem peelTower_zero_eq (hd : 1 ≤ d + 1) (m : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    peelTower U d hd m a 0 = pull (cpPrU U d) m (a 0) := rfl

/-- The tower's successor equation with the degree written as `m + 2 * k + 2`
rather than `m + 2 * (k + 1)`.  Both are `rfl`, but only this form lets `pull_cup`
split the degree, since the pattern `?p + ?q` has to see the summand boundary. -/
theorem peelTower_succ_eq (hd : 1 ≤ d + 1) (m k : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    peelTower U d hd m a (k + 1)
      = pull (cpPrU U d) (m + 2 * k + 2) (a (k + 1))
        + cup (peelTower U d hd m a k)
            (pull (cpPrCP U d) 2 (cpGen (d + 1) hd)) := rfl

/-! ## 3. A tower restricts to the tower -/

set_option maxHeartbeats 1000000 in
/-- **The restriction of a tower is the tower at the smaller rank**, with the same
coefficients and the same base degree.  Base pullbacks restrict to base pullbacks
and the generator restricts to the generator, so nothing is reindexed. -/
theorem pull_sInclusion_peelTower (hd1 : 1 ≤ d + 1 + 1) (hd : 1 ≤ d + 1) (m : ℕ)
    (a : (j : ℕ) → Hmod2 (TopCat.of U) (m + 2 * j)) :
    ∀ k : ℕ,
      pull (sInclusion (punctUSet U (d + 1))) (m + 2 * k)
          (peelTower U (d + 1) hd1 m a k)
        = pull (cmap (punctHomotopyEquiv U (d + 1)).toFun) (m + 2 * k)
            (peelTower U d hd m a k) := by
  intro k
  induction k with
  | zero =>
    show pull (sInclusion (punctUSet U (d + 1))) m (peelTower U (d + 1) hd1 m a 0)
      = pull (cmap (punctHomotopyEquiv U (d + 1)).toFun) m (peelTower U d hd m a 0)
    rw [peelTower_zero_eq, peelTower_zero_eq, pull_sInclusion_cpPrU, pull_punctHE_prU]
  | succ e ih =>
    show pull (sInclusion (punctUSet U (d + 1))) (m + 2 * e + 2)
        (peelTower U (d + 1) hd1 m a (e + 1))
      = pull (cmap (punctHomotopyEquiv U (d + 1)).toFun) (m + 2 * e + 2)
        (peelTower U d hd m a (e + 1))
    rw [peelTower_succ_eq, peelTower_succ_eq, pull_add, pull_cup,
      pull_sInclusion_cpPrU, ih, pull_sInclusion_cpPrCP_cpGen U (d + 1) hd hd1,
      ← pull_cup, ← pull_punctHE_prU, ← pull_add]

/-! ## 4. Freeness -/

set_option maxHeartbeats 1000000 in
/-- **Freeness of the tower, at every rank.**  Induction on the rank: the
restriction supplies every coefficient whose power survives below, and the
escaping index is the one whose power is the top power here. -/
theorem peelFreeAt (d : ℕ) : PeelFreeAt d := by
  induction d with
  | zero =>
    intro U _ hd m k a hzero j hj hkj
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact peelTower_top_coeff_eq_zero U 0 hd m j a hzero
    · have hk : k = j + (0 + 1) := by omega
      subst hk
      refine peelTower_top_index_eq_zero_all U 0 hd m j a ?_ hzero
      intro j' h1 h2
      have hj' : j' = j + (0 + 1) := by omega
      subst hj'
      exact peelTower_top_coeff_eq_zero U 0 hd m (j + (0 + 1)) a hzero
  | succ e ih =>
    intro U _ hd1 m k a hzero j hj hkj
    have hde : 1 ≤ e + 1 := by omega
    have hres : peelTower U e hde m a k = 0 := by
      have h1 := pull_sInclusion_peelTower U e hd1 hde m a k
      rw [hzero, pull_zero] at h1
      refine (punctPullEquiv U (e + 1) (m + 2 * k)).injective ?_
      rw [map_zero]
      exact h1.symm
    rcases Nat.lt_or_ge (k - j) (e + 1 + 1) with hlt | hge
    · exact ih U hde m k a hres j hj (by omega)
    · have hk : k = j + (e + 1 + 1) := by omega
      subst hk
      refine peelTower_top_index_eq_zero_all U (e + 1) hd1 m j a ?_ hzero
      intro j' h1 h2
      exact ih U hde m (j + (e + 1 + 1)) a hres j' (by omega) (by omega)

/-- The bounded specialisation, for consumers that want it. -/
theorem peelFree (d : ℕ) : PeelFree d :=
  peelFree_of_peelFreeAt d (peelFreeAt d)

end KnCP

end

end GroupApproximation.CharClass
