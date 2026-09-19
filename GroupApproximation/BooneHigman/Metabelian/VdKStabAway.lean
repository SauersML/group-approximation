import GroupApproximation.StableRange.Instances
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable range of `ℤ[1/m]`

`vdkStab_stableRangeLE_away`: Bass's stable range condition `sr(ℤ[1/m]) ≤ 2`, for every `m`.

Lane pal-q111 first proved this (ba8e283846) from the PID bound `vdkStab_stableRangeLE_two_of_pid`, using
`Absorption.suslinKill_away_pid` and `CharZeroHost.isDomain_away`, with the zero ring at `m = 0` as a
separate case.  It now derives from the general bound `sr ≤ dim + 1`
(`StableRange.stableRangeLE_away`, lane fix-bh-a): `dim ℤ[1/m] ≤ 1` for every `m`.  This covers
`m = 0` too, and drops the imports of `SuslinKillLift` and `CharZeroHost.ZInv`.

This is the stable-range input at the base ring of the characteristic-zero `K₂` gap `Z1`:
injective stability in the range `N ≥ sr + 3` (`vdkStab_InjStabStatement`) applies to
`K₂(N, ℤ[1/m])` exactly for `N ≥ 5`, the rank of `CharZeroK2BaseFGStatement`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **`sr(ℤ[1/m]) ≤ 2`**, for every `m`. -/
theorem vdkStab_stableRangeLE_away (m : ℕ) :
    vdkStab_StableRangeLE (Localization.Away (m : ℤ)) 2 :=
  GroupApproximation.StableRange.stableRangeLE_away m

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkStab_stableRangeLE_away

end GroupApproximation.BooneHigman.Metabelian.ElemFP
