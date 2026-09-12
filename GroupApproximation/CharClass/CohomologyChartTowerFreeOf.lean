import GroupApproximation.CharClass.CohomologyChartTowerOf

/-!
# Freeness of the peel tower over a field: the ingredients

The coefficient-generic form of `CohomologyChartTowerFree`.  The two ends of the rank induction
are the slice argument and need no hypothesis.  The collapse step identifies the connecting class
with the top power of the fibre class: over `F₂` the two are *equal*, because `H^{2d+2}(ℂP^{d+1})`
is a line with one nonzero element; over `K` they differ by a **nonzero scalar**, since both are
nonzero in a line, and a nonzero scalar is all the collapse needs.

## Main declarations

* `KnCP.peel_base_eq_zero_rightOf`, `KnCP.peelTower_zero_eq_zeroOf`,
  `KnCP.peelTower_succ_top_eq_zeroOf` — the top coefficient always dies.
* `KnCP.cpTopPtOf_ne_zeroOf` — the connecting class is nonzero at every rank, over the ring input.
* `KnCP.cupPowE_eq_smul_cpTopPtOf` — **the top power is a nonzero multiple of the connecting
  class**.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. The top coefficient always dies -/

set_option maxHeartbeats 1000000 in
/-- The slice argument with the class on the right, over `K`. -/
theorem peel_base_eq_zero_rightOf (h : Hmod K (CPtop (d + 1)) 2) (n : ℕ)
    (a : Hmod K (TopCat.of U) (n + 2)) (y : Hmod K (cpProdTop U d) n)
    (hsum : pull (cpPrU U d) (n + 2) a + cup y (pull (cpPrCP U d) 2 h) = 0) : a = 0 := by
  obtain ⟨p⟩ := nonempty_CPtop (d + 1)
  have hconst : pull (cpSliceGen U (d + 1) p ≫ cpPrCP U d) 2 h = 0 := by
    rw [cpSliceGen_comp_cpPrCP]
    exact pull_const_eq_zeroOf K U p 2 (by omega) h
  have hs := congrArg (pull (cpSliceGen U (d + 1) p) (n + 2)) hsum
  rw [pull_add, pull_zero, ← pull_comp, cpSliceGen_comp_cpFst, pull_id, pull_cup,
    ← pull_comp, hconst, cup_zero, add_zero] at hs
  exact hs

/-- A tower of length zero determines its one coefficient. -/
theorem peelTower_zero_eq_zeroOf (h : Hmod K (CPtop (d + 1)) 2) (m : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    (hz : peelTowerOf K U d h m a 0 = 0) : a 0 = 0 := by
  simp only [peelTowerOf] at hz
  refine pull_cpFst_injectiveOf K U (d + 1) (m + 2 * 0) ?_
  rw [pull_zero]
  exact hz

set_option maxHeartbeats 1000000 in
/-- **The top coefficient of a vanishing tower vanishes, with no bound**, and what is left is the
shorter tower cupped with the class. -/
theorem peelTower_succ_top_eq_zeroOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    (hz : peelTowerOf K U d h m a (k + 1) = 0) :
    a (k + 1) = 0 ∧
      cup (peelTowerOf K U d h m a k) (pull (cpPrCP U d) 2 h) = 0 := by
  simp only [peelTowerOf] at hz
  have htop : a (k + 1) = 0 :=
    peel_base_eq_zero_rightOf K U d h (m + 2 * k) (a (k + 1)) (peelTowerOf K U d h m a k) hz
  refine ⟨htop, ?_⟩
  rw [htop, pull_zero, zero_add] at hz
  exact hz

/-! ## 2. The connecting class and the top power -/

set_option maxHeartbeats 1000000 in
/-- **The connecting class of the chart cover is nonzero at every rank**, over the ring input. -/
theorem cpTopPtOf_ne_zeroOf (hring : CPRingOf K) (d : ℕ) : cpTopPtOf K d ≠ 0 := by
  match d with
  | 0 => exact cpTopPtOf_zero_ne_zero K
  | (e + 1) =>
    intro h0
    haveI : Nonempty ↥(TopCat.of Unit) := ⟨()⟩
    have hz : cup (cpTopOf K Unit (e + 1))
        (pull (cpPrU Unit (e + 1)) 0 (one (TopCat.of Unit))) = 0 := by
      rw [cpTopOf_eq_pull_cpTopPtOf, h0, pull_zero, zero_cup]
    exact one_ne_zero_cohZeroOf K (TopCat.of Unit)
      (cpTop_cup_injective_closedOf K Unit (e + 1) hring (by omega) 0 (one (TopCat.of Unit)) hz)

/-- **The top power of a nonzero class is a nonzero multiple of the connecting class**: both are
nonzero in the line `H^{2d+2}(ℂP^{d+1}; K)`. -/
theorem cupPowE_eq_smul_cpTopPtOf (hring : CPRingOf K) (h : Hmod K (CPtop (d + 1)) 2)
    (h0 : h ≠ 0) : ∃ c : K, c ≠ 0 ∧ cupPowE h (d + 1) = c • cpTopPtOf K d := by
  obtain ⟨L⟩ := (hasCPCohomologyOf_CP K (d + 1)).1 (d + 1) le_rfl
  exact exists_ne_zero_smul_of_line L (cpTopPtOf_ne_zeroOf K hring d)
    (hring (d + 1) (by omega) h h0 (d + 1) le_rfl)

end KnCP

end

end GroupApproximation.CharClass
