import GroupApproximation.CharClass.CohomologyChartTowerCollapseOf

/-!
# The one index a rank restriction cannot see, over a field

The coefficient-generic form of `CohomologyChartTowerTop`: powers of the pulled-back class past the
fibre dimension vanish, and a tower cupped with the top power keeps only its escaping
coefficient.

## Main declarations

* `KnCP.cupPowE_pull_eq_zeroOf`, `KnCP.cup_gen_cupPowE_top_eq_zeroOf`.
* `KnCP.peelTower_top_coeff_eq_zeroOf` — the last coefficient of a vanishing tower vanishes.
* `KnCP.cup_peelTower_cupPowE_topOf` — only the escaping coefficient survives the top power.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **Powers of the pulled-back class past the fibre dimension vanish on the product.** -/
theorem cupPowE_pull_eq_zeroOf (h : Hmod K (CPtop (d + 1)) 2) (p : ℕ) (hp : d + 1 < p) :
    cupPowE (pull (cpPrCP U d) 2 h) p = 0 := by
  rw [← pull_cupPowE,
    cupPowE_eq_zero_of_gt h (d + 1) (hasCPCohomologyOf_CP K (d + 1)) hp, pull_zero]

/-- One more class past the top power is zero, with the class on the left. -/
theorem cup_gen_cupPowE_top_eq_zeroOf (h : Hmod K (CPtop (d + 1)) 2) :
    cup (pull (cpPrCP U d) 2 h) (cupPowE (pull (cpPrCP U d) 2 h) (d + 1)) = 0 := by
  rw [cup_comm_of_even_left even_two, ← cupPowE_succ,
    cupPowE_pull_eq_zeroOf K U d h (d + 1 + 1) (by omega), cohCast_zero]

/-- **The last coefficient of a vanishing tower vanishes**, at any rank and with no hypothesis. -/
theorem peelTower_top_coeff_eq_zeroOf (h : Hmod K (CPtop (d + 1)) 2) (m k : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j))
    (hz : peelTowerOf K U d h m a k = 0) : a k = 0 := by
  match k with
  | 0 => exact peelTower_zero_eq_zeroOf K U d h m a hz
  | (k' + 1) => exact (peelTower_succ_top_eq_zeroOf K U d h m k' a hz).1

set_option maxHeartbeats 1000000 in
/-- Below the escaping index every power has run past the fibre dimension, so only the escaping
coefficient survives the top power. -/
theorem cup_peelTower_cupPowE_topOf (h : Hmod K (CPtop (d + 1)) 2) (m j₀ : ℕ)
    (a : (j : ℕ) → Hmod K (TopCat.of U) (m + 2 * j)) :
    cup (peelTowerOf K U d h m a j₀) (cupPowE (pull (cpPrCP U d) 2 h) (d + 1))
      = cup (pull (cpPrU U d) (m + 2 * j₀) (a j₀))
          (cupPowE (pull (cpPrCP U d) 2 h) (d + 1)) := by
  match j₀ with
  | 0 => simp only [peelTowerOf]
  | (j' + 1) =>
    simp only [peelTowerOf]
    rw [cup_add_left, cup_assoc', cup_gen_cupPowE_top_eq_zeroOf K U d h, cup_zero,
      cohCast_zero, add_zero]

end KnCP

end

end GroupApproximation.CharClass
