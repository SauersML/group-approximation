import GroupApproximation.CharClass.CohomologyChartLowDegreeOf
import GroupApproximation.CharClass.CohomologyChartPeelUniq

/-!
# One peel over a field: the base coefficient is determined

The coefficient-generic form of `CohomologyChartPeelUniq`.  The slice through a point of the fibre
recovers the base coefficient of a peel and kills any degree-two class from the fibre, so the base
coefficient is unique, at every rank and with no hypothesis.

## Main declarations

* `KnCP.lhLow_genOf` — the floor at the peeling index.
* `KnCP.peel_base_eq_zeroOf`, `KnCP.cup_gen_eq_zero_of_peel_zeroOf`.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K] (U : Type) [TopologicalSpace U] (d : ℕ)

/-- **The floor of the ladder at the peeling index**, over `K`. -/
theorem lhLow_genOf (n : ℕ) (hn : n < 2) :
    Function.Bijective (pull (K := K) (cpPrU U d) n) :=
  lhLow_generalOf K U (d + 1) n hn

set_option maxHeartbeats 1000000 in
/-- **The base coefficient of a peel is determined**, over `K`, for any degree-two class. -/
theorem peel_base_eq_zeroOf (h : Hmod K (CPtop (d + 1)) 2) (n : ℕ)
    (a : Hmod K (TopCat.of U) (2 + n)) (y : Hmod K (cpProdTop U d) n)
    (hsum : pull (cpPrU U d) (2 + n) a + cup (pull (cpPrCP U d) 2 h) y = 0) : a = 0 := by
  obtain ⟨p⟩ := nonempty_CPtop (d + 1)
  have hconst : pull (cpSliceGen U (d + 1) p ≫ cpPrCP U d) 2 h = 0 := by
    rw [cpSliceGen_comp_cpPrCP]
    exact pull_const_eq_zeroOf K U p 2 (by omega) h
  have hs := congrArg (pull (cpSliceGen U (d + 1) p) (2 + n)) hsum
  rw [pull_add, pull_zero, ← pull_comp, cpSliceGen_comp_cpFst, pull_id, pull_cup,
    ← pull_comp, hconst, zero_cup, add_zero] at hs
  exact hs

/-- **And the rest of a vanishing peel is exactly a kernel element**, over `K`. -/
theorem cup_gen_eq_zero_of_peel_zeroOf (h : Hmod K (CPtop (d + 1)) 2) (n : ℕ)
    (a : Hmod K (TopCat.of U) (2 + n)) (y : Hmod K (cpProdTop U d) n)
    (hsum : pull (cpPrU U d) (2 + n) a + cup (pull (cpPrCP U d) 2 h) y = 0) :
    cup (pull (cpPrCP U d) 2 h) y = 0 := by
  rw [peel_base_eq_zeroOf K U d h n a y hsum, pull_zero, zero_add] at hsum
  exact hsum

end KnCP

end

end GroupApproximation.CharClass
