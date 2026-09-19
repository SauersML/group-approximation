import GroupApproximation.BooneHigman.Metabelian.VdKStabPID
import GroupApproximation.BooneHigman.Metabelian.CharZeroHost.ZInv
import GroupApproximation.BooneHigman.Metabelian.SuslinKillLift
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable range of `ℤ[1/m]`

`vdkStab_stableRangeLE_away`: Bass's stable range condition `sr(ℤ[1/m]) ≤ 2`, for every `m`.
For `m ≠ 0`, `ℤ[1/m]` is a principal ideal domain (`Absorption.suslinKill_away_pid`,
`CharZeroHost.isDomain_away`), so this is `vdkStab_stableRangeLE_two_of_pid`.  For `m = 0` the
ring is zero (`CharZeroHost.away_zero_eq_one`), and every row is unimodular.

This is the stable-range input at the base ring of the characteristic-zero `K₂` gap `Z1`:
injective stability in the range `N ≥ sr + 3` (`vdkStab_InjStabStatement`) applies to
`K₂(N, ℤ[1/m])` exactly for `N ≥ 5`, the rank of `CharZeroK2BaseFGStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **`sr(ℤ[1/m]) ≤ 2`**, for every `m`. -/
theorem vdkStab_stableRangeLE_away (m : ℕ) :
    vdkStab_StableRangeLE (Localization.Away (m : ℤ)) 2 := by
  by_cases hm : m = 0
  · intro n _ v _
    refine ⟨0, (vdkStab_isUnimodular_iff _).2 ?_⟩
    rw [← CharZeroHost.away_zero_eq_one hm]
    exact Ideal.zero_mem _
  · haveI : IsDomain (Localization.Away (m : ℤ)) := CharZeroHost.isDomain_away hm
    haveI : IsPrincipalIdealRing (Localization.Away (m : ℤ)) := Absorption.suslinKill_away_pid m
    exact vdkStab_stableRangeLE_two_of_pid (Localization.Away (m : ℤ))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_stableRangeLE_away

end GroupApproximation.BooneHigman.Metabelian.ElemFP
