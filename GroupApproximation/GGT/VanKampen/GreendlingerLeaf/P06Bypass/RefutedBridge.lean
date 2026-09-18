import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.RefutedCore
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFiveInterface
import GroupApproximation.Meta.AxiomGuard

/-!
# Bridge between the two copies of the refuted walk binder

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `gl-p06-01`.

Lane gl-p06-02 stated the same interface in the sub-namespace `P06Bypass.BinderFive`
(`BinderFiveInterface.lean`), because this lane's `RefutedDef.lean` was not on disk yet.  The two
definitions have identical bodies, so each section statement is the other by unfolding.  This module
records both directions and the P07 reductions in the `BinderFive` form, so consumers of either copy
can use the reductions of `RefutedCore.lean`.

## Manuscript status

Infrastructure for `thm:hull`; certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

universe u w v

/-- The refuted section statement in the `BinderFive` form: the bodies agree by unfolding. -/
theorem refutedBelowSection_toBinderFive
    (h : CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    BinderFive.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  h

/-- The `BinderFive` form gives the refuted section statement: the bodies agree by unfolding. -/
theorem refutedBelowSection_ofBinderFive
    (h : BinderFive.CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  h

/-- **The `BinderFive` refuted section statement from the long-word inner two-arc residual.** -/
theorem binderFiveRefutedBelowSection_of_innerTwoArcLong
    (h : P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v}) :
    BinderFive.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  refutedBelowSection_toBinderFive (refutedBelowSection_of_innerTwoArcLong h)

/-- **The `BinderFive` refuted section statement from the enclosed inner pocket.** -/
theorem binderFiveRefutedBelowSection_of_innerPocketEnclosed
    (h : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
    BinderFive.CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  refutedBelowSection_toBinderFive (refutedBelowSection_of_innerPocketEnclosed h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.refutedBelowSection_toBinderFive
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.refutedBelowSection_ofBinderFive
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.binderFiveRefutedBelowSection_of_innerTwoArcLong
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.binderFiveRefutedBelowSection_of_innerPocketEnclosed
