import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFiveSection
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.WaistInterface
import GroupApproximation.Meta.AxiomGuard

/-!
# The binder-5 interface of the bypass waist, discharged

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `gl-p06-02`.

Lane gl-p06-03 states the theorem of this lane as a Prop, `Waist.BinderFiveOfRefutedStatement`
(`WaistInterface.lean`), in the sub-namespace `P06Bypass.Waist`, with its own copy of the refuted
walk binder.  That copy has the body of `CellPocketWalkRefutedBelowSectionStatement`
(`RefutedDef.lean`), so the Prop is `osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`
(`BinderFiveSection.lean`) by unfolding.

* `binderFiveOfRefutedStatement_closed : Waist.BinderFiveOfRefutedStatement`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

universe u w v

/-- **The binder-5 interface of the bypass waist holds**: binder 5 below the bound from the refuted
section binder (`osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`). -/
theorem binderFiveOfRefutedStatement_closed : Waist.BinderFiveOfRefutedStatement.{u, w, v} :=
  by
  intro h
  exact osinMultipleEdgePocketRegionCopyBelowSection_of_refuted h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.binderFiveOfRefutedStatement_closed
