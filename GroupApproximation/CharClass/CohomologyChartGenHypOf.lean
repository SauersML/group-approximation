import GroupApproximation.CharClass.CohomologyChartSplitOf
import GroupApproximation.CharClass.ProjectiveSpaceRing

/-!
# Generation on `ℂP^e` over a field, from the nonvanishing of powers

The coefficient-generic form of `ProjectiveSpaceGenHyp.cpGenHyp_of_cupPowE_ne_zero`.  Outside the
even degrees up to `2e` the group vanishes and zero works; inside, the group is a line
(`hasCPCohomologyOf_CP`), so a class is a scalar multiple of the corresponding power of any nonzero
degree-two class whose powers survive, and that power is the class cupped with the power below it.
Over `F₂` the scalar was `0` or `1`; over `K` it rides along through `cup_smul_right`.

## Main declarations

* `KnCP.cpGenHypOf_of_cupPowE_ne_zeroOf` — **generation, from the ring statement**.
-/

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.CPn

namespace GroupApproximation.CharClass

noncomputable section

namespace KnCP

variable (K : Type) [Field K]

/-- **Cupping with a nonzero degree-two class is surjective onto positive degrees**, given that its
powers up to the dimension are nonzero. -/
theorem cpGenHypOf_of_cupPowE_ne_zeroOf (e : ℕ)
    (hne : ∀ (h : Hmod K (CPtop e) 2), h ≠ 0 → ∀ m : ℕ, m ≤ e → cupPowE h m ≠ 0) :
    CPGenHypOf K e := by
  intro h h0 k c
  by_cases hk : ∃ j : ℕ, 2 + k = 2 * (j + 1) ∧ j + 1 ≤ e
  · obtain ⟨j, he, hje⟩ := hk
    have hkj : k = 2 * j := by omega
    subst hkj
    obtain ⟨L⟩ := (hasCPCohomologyOf_CP K e).1 (j + 1) hje
    obtain ⟨c₀, hc₀⟩ := exists_smul_of_line L (hne h h0 (j + 1) hje) (cohCast he c)
    refine ⟨c₀ • cupPowE h j, ?_⟩
    have h2 : c = cohCast he.symm (c₀ • cupPowE h (j + 1)) := by
      rw [← hc₀, cohCast_cohCast, cohCast_self]
    rw [h2, cup_smul_right, cohCast_smul]
    congr 1
    show cohCast he.symm (cup (cupPowE h j) h) = _
    rw [cup_comm_of_even_right even_two, cohCast_cohCast]
    exact cohCast_self _ _
  · refine ⟨0, ?_⟩
    rw [cup_zero]
    refine (hasCPCohomologyOf_CP K e).2 (2 + k) ?_ c
    intro n hn hcontra
    exact hk ⟨n - 1, by omega, by omega⟩

end KnCP

end

end GroupApproximation.CharClass
