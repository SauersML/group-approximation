import GroupApproximation.Dynamics.InvolutionLocalizationRing
import GroupApproximation.Dynamics.ChainRecurrenceCovering
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:involution-localization`, finite-field clause: closed

`non_mf_groups_exist.tex`, `\label{lem:involution-localization}` (tex 1663–1667):

> Let $C$ be a full clopen section with bounded positive return times, put $p_C=1_C$ and
> $J=p_CIp_C$.  Over any finite field, for every finite $F\subset I$ there is $w\in R_X^\times$ with
> $w-1\in I$, $w^2=1$, and $wFw^{-1}\subset J$.

The only piece of `involutionLocalizationRingClause_of_cover` is the defect cover of
lem:chain-core-models (tex 1373–1375), in the spelling `ChainCoreDefectCoverStatement`.  It follows
from the landed `Dynamics.exists_isClopen_apply_mem_diff`: a point `x` off the chain-recurrent set
has a compressed clopen `P` with `Tx ∈ P ∖ T(P)`, so `x` lies in the translate `T⁻¹(P ∖ T(P))`.

* `chainCoreDefectCoverStatement_holds : ChainCoreDefectCoverStatement`;
* `involutionLocalizationRingClause_closed : InvolutionLocalizationRingClause`.
-/

namespace GroupApproximation

namespace ClopenCrossedProduct

/-- The defect cover of lem:chain-core-models (tex 1373–1375), in the spelling consumed by
lem:involution-localization. -/
theorem chainCoreDefectCoverStatement_holds : ChainCoreDefectCoverStatement := by
  intro X _ _ _ _ T x hx
  obtain ⟨P, hPc, hPT, hxP⟩ := Dynamics.exists_isClopen_apply_mem_diff T hx
  refine ⟨P, hPc, -1, hPT, T x, hxP, ?_⟩
  rw [zpow_neg_one, Homeomorph.inv_apply, Homeomorph.symm_apply_apply]

/-- **lem:involution-localization, finite-field clause** (tex 1664–1667), closed. -/
theorem involutionLocalizationRingClause_closed : InvolutionLocalizationRingClause :=
  involutionLocalizationRingClause_of_cover chainCoreDefectCoverStatement_holds

end ClopenCrossedProduct

end GroupApproximation

#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.chainCoreDefectCoverStatement_holds
#audit_closed_axioms GroupApproximation.ClopenCrossedProduct.involutionLocalizationRingClause_closed
