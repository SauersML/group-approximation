import GroupApproximation.CharClass.CohomologyChartTowerFreeOf

/-!
# A tower with no coefficients above `j₀` is a shorter tower times a power, over a field

The coefficient-generic form of `CohomologyChartTowerCollapse`: freeness stated index by index,
and the collapse of a tower whose coefficients above `j₀` vanish.

## Main declarations

* `KnCP.PeelFreeAtOf` — freeness index by index, for every nonzero fibre class.
* `KnCP.peelTower_eq_cup_powOf` — **the collapse**.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

/-- **Freeness stated index by index, over `K`.**  A coefficient of a vanishing tower vanishes as
soon as its own power survives the rank, for every nonzero fibre class. -/
def PeelFreeAtOf (K : Type) [Field K] (d : ℕ) : Prop :=
  ∀ (U : Type) [TopologicalSpace U] (h : Hmod K (CPtop (d + 1)) 2), h ≠ 0 →
    ∀ (m k : ℕ) (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)),
      peelTowerOf K U d h m a k = 0 → ∀ j, j ≤ k → k - j ≤ d + 1 → a j = 0

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

set_option maxHeartbeats 1000000 in
/-- **A tower whose coefficients above `j₀` all vanish is the tower truncated at `j₀`, cupped with
a power of the class.** -/
theorem peelTower_eq_cup_powOf (h : Hmod K (CPtop (d + 1)) 2) (m j₀ : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    ∀ p : ℕ, (∀ j, j₀ < j → j ≤ j₀ + p → a j = 0) →
      peelTowerOf K U d h m a (j₀ + p)
        = cohCast (show m + 2 * j₀ + 2 * p = m + 2 * (j₀ + p) by omega)
            (cup (peelTowerOf K U d h m a j₀)
              (cupPowE (pull (cpPrCP U d) 2 h) p)) := by
  intro p
  induction p with
  | zero =>
    intro _
    rw [cupPowE_zero, cup_one]
    exact rfl
  | succ q ih =>
    intro hz
    have ha : a (j₀ + q + 1) = 0 := hz (j₀ + q + 1) (by omega) (by omega)
    have hstep : peelTowerOf K U d h m a (j₀ + (q + 1))
        = cup (peelTowerOf K U d h m a (j₀ + q)) (pull (cpPrCP U d) 2 h) := by
      show peelTowerOf K U d h m a (j₀ + q + 1) = _
      simp only [peelTowerOf]
      rw [ha, pull_zero, zero_add]
    rw [hstep, ih (fun j hj1 hj2 => hz j hj1 (by omega)), cup_cohCast_left,
      cup_assoc', cohCast_cohCast, ← cupPowE_succ]

end KnCP

end

end GroupApproximation.CharClass
