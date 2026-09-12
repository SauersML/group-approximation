import GroupApproximation.CharClass.CohomologyChartTowerTopOf

/-!
# Freeness of the peel tower over a field, over the ring input

The coefficient-generic form of `CohomologyChartFreeness`.  The induction is on the rank, exactly
as over `F₂`: restricting a vanishing tower to the punctured piece gives the tower at the smaller
rank with the same coefficients, against the restricted class `pull (cpIncl (d+1)) 2 h`, which is
nonzero; the one escaping index is reached through the collapse, where the top power is a nonzero
multiple of the connecting class (`cupPowE_eq_smul_cpTopPtOf`) and the scalar is cancelled.

## Main declarations

* `KnCP.cpTop_cup_injective_allOf` — injectivity of the top class at every rank.
* `KnCP.peelTower_top_index_eq_zero_allOf` — the escaping index.
* `KnCP.pull_sInclusion_peelTowerOf` — a tower restricts to the tower.
* `KnCP.peelFreeAtOf` — **freeness, at every rank, over the ring input**.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-! ## 1. Injectivity of the top class at every rank -/

/-- **The top class is injective on pullbacks at every rank**, over the ring input; at the lowest
rank no input is used. -/
theorem cpTop_cup_injective_allOf (hring : CPRingOf K) (m : ℕ) (b : Hmod K (TopCat.of U) m)
    (hcup : cup (cpTopOf K U d) (pull (cpPrU U d) m b) = 0) : b = 0 := by
  match d with
  | 0 => exact cpTop_cup_injective_zeroOf K U m b hcup
  | (e + 1) => exact cpTop_cup_injective_closedOf K U (e + 1) hring (by omega) m b hcup

set_option maxHeartbeats 1000000 in
/-- **The escaping index**, over `K`. -/
theorem peelTower_top_index_eq_zero_allOf (hring : CPRingOf K) (h : Hmod K (CPtop (d + 1)) 2)
    (h0 : h ≠ 0) (m j₀ : ℕ) (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    (hhi : ∀ j, j₀ < j → j ≤ j₀ + (d + 1) → a j = 0)
    (hzero : peelTowerOf K U d h m a (j₀ + (d + 1)) = 0) : a j₀ = 0 := by
  have hcol := peelTower_eq_cup_powOf K U d h m j₀ a (d + 1) hhi
  have hz : cup (peelTowerOf K U d h m a j₀) (cupPowE (pull (cpPrCP U d) 2 h) (d + 1)) = 0 :=
    (cohCast_eq_zero_iff _ _).mp (hcol.symm.trans hzero)
  rw [cup_peelTower_cupPowE_topOf K U d h m j₀ a] at hz
  obtain ⟨c, hc, hcpow⟩ := cupPowE_eq_smul_cpTopPtOf K d hring h h0
  rw [← pull_cupPowE, hcpow, pull_smul, cup_smul_right] at hz
  have hz' : cup (pull (cpPrU U d) (m + 2 * j₀) (a j₀))
      (pull (cpPrCP U d) (2 * (d + 1)) (cpTopPtOf K d)) = 0 := by
    have h1 : c⁻¹ • c • cup (pull (cpPrU U d) (m + 2 * j₀) (a j₀))
        (pull (cpPrCP U d) (2 * (d + 1)) (cpTopPtOf K d)) = c⁻¹ • (0 : Hmod K (cpProdTop U d)
          (m + 2 * j₀ + 2 * (d + 1))) := by
      rw [hz]
    rw [smul_zero, smul_smul, inv_mul_cancel₀ hc, one_smul] at h1
    exact h1
  have htop : cup (pull (cpPrU U d) (m + 2 * j₀) (a j₀)) (cpTopOf K U d) = 0 := by
    rw [cpTopOf_eq_pull_cpTopPtOf]
    exact hz'
  refine cpTop_cup_injective_allOf K U d hring (m + 2 * j₀) (a j₀) ?_
  rw [cup_comm_of_even_left ⟨d + 1, by omega⟩ (cpTopOf K U d)
      (pull (cpPrU U d) (m + 2 * j₀) (a j₀)), htop, cohCast_zero]

/-! ## 2. The tower's equations at normalised degrees -/

theorem peelTower_zero_eqOf (h : Hmod K (CPtop (d + 1)) 2) (m : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    peelTowerOf K U d h m a 0 = pull (cpPrU U d) m (a 0) := rfl

theorem peelTower_succ_eqOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    peelTowerOf K U d h m a (k + 1)
      = pull (cpPrU U d) (m + 2 * k + 2) (a (k + 1))
        + cup (peelTowerOf K U d h m a k) (pull (cpPrCP U d) 2 h) := rfl

/-! ## 3. A tower restricts to the tower -/

set_option maxHeartbeats 1000000 in
/-- **The restriction of a tower is the tower at the smaller rank**, with the same coefficients,
against the restricted class. -/
theorem pull_sInclusion_peelTowerOf (h : Hmod K (CPtop (d + 1 + 1)) 2) (m : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    ∀ k : ℕ,
      pull (sInclusion (punctUSet U (d + 1))) (m + 2 * k)
          (peelTowerOf K U (d + 1) h m a k)
        = pull (cmap (punctHomotopyEquiv U (d + 1)).toFun) (m + 2 * k)
            (peelTowerOf K U d (pull (cpIncl (d + 1)) 2 h) m a k) := by
  intro k
  induction k with
  | zero =>
    show pull (sInclusion (punctUSet U (d + 1))) m (peelTowerOf K U (d + 1) h m a 0)
      = pull (cmap (punctHomotopyEquiv U (d + 1)).toFun) m
          (peelTowerOf K U d (pull (cpIncl (d + 1)) 2 h) m a 0)
    rw [peelTower_zero_eqOf, peelTower_zero_eqOf, pull_sInclusion_cpPrUOf, pull_punctHE_prUOf]
  | succ e ih =>
    show pull (sInclusion (punctUSet U (d + 1))) (m + 2 * e + 2)
        (peelTowerOf K U (d + 1) h m a (e + 1))
      = pull (cmap (punctHomotopyEquiv U (d + 1)).toFun) (m + 2 * e + 2)
        (peelTowerOf K U d (pull (cpIncl (d + 1)) 2 h) m a (e + 1))
    rw [peelTower_succ_eqOf, peelTower_succ_eqOf, pull_add, pull_cup,
      pull_sInclusion_cpPrUOf, ih, pull_sInclusion_cpPrCP_hOf K U (d + 1) h,
      ← pull_cup, ← pull_punctHE_prUOf, ← pull_add]

/-! ## 4. Freeness -/

set_option maxHeartbeats 1000000 in
/-- **Freeness of the tower over `K`, at every rank, over the ring input.** -/
theorem peelFreeAtOf (hring : CPRingOf K) (d : ℕ) : PeelFreeAtOf K d := by
  induction d with
  | zero =>
    intro U _ h h0 m k a hzero j hj hkj
    rcases Nat.eq_or_lt_of_le hj with rfl | hlt
    · exact peelTower_top_coeff_eq_zeroOf K U 0 h m j a hzero
    · have hk : k = j + (0 + 1) := by omega
      subst hk
      refine peelTower_top_index_eq_zero_allOf K U 0 hring h h0 m j a ?_ hzero
      intro j' h1 h2
      have hj' : j' = j + (0 + 1) := by omega
      subst hj'
      exact peelTower_top_coeff_eq_zeroOf K U 0 h m (j + (0 + 1)) a hzero
  | succ e ih =>
    intro U _ h h0 m k a hzero j hj hkj
    have hres : peelTowerOf K U e (pull (cpIncl (e + 1)) 2 h) m a k = 0 := by
      have h1 := pull_sInclusion_peelTowerOf K U e h m a k
      rw [hzero, pull_zero] at h1
      refine (punctPullEquivOf K U (e + 1) (m + 2 * k)).injective ?_
      rw [map_zero]
      exact h1.symm
    have h0' := pull_cpIncl_ne_zeroOf K (e + 1) (by omega) h h0
    rcases Nat.lt_or_ge (k - j) (e + 1 + 1) with hlt | hge
    · exact ih U (pull (cpIncl (e + 1)) 2 h) h0' m k a hres j hj (by omega)
    · have hk : k = j + (e + 1 + 1) := by omega
      subst hk
      refine peelTower_top_index_eq_zero_allOf K U (e + 1) hring h h0 m j a ?_ hzero
      intro j' h1 h2
      exact ih U (pull (cpIncl (e + 1)) 2 h) h0' m (j + (e + 1 + 1)) a hres j' (by omega)
        (by omega)

end KnCP

end

end GroupApproximation.CharClass
