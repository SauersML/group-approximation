import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.RefutedDef
import GroupApproximation.Meta.AxiomGuard

/-!
# Compatibility names for the refuted walk binder

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b), lane `gl-p06-02`.

When lane gl-p06-02 started, lane gl-p06-01's `RefutedDef.lean` was not on disk, so this module
stated the refuted walk binder in the sub-namespace `P06Bypass.BinderFive`.  `RefutedDef.lean` has
since landed, and `RefutedBridge.lean` refers to the `BinderFive` names.  This module keeps those
names as abbreviations of the landed definitions, so there is one body and no duplicate
declaration.

* `BinderFive.CellPocketWalkRefutedBelowInput` is `P06Bypass.CellPocketWalkRefutedBelowInput`.
* `BinderFive.CellPocketWalkRefutedBelowSectionStatement` is
  `P06Bypass.CellPocketWalkRefutedBelowSectionStatement`.
* `BinderFive.CellPocketWalkRefutedBelowInput.toProperArcs` and
  `BinderFive.properArcsBelowSection_of_refuted`: the refuted binder gives the proper arcs.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive

universe u w v

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The walk binder of the below proper arcs is refuted**: the landed
`P06Bypass.CellPocketWalkRefutedBelowInput`. -/
abbrev CellPocketWalkRefutedBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  P06Bypass.CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W

/-- The refuted binder gives the below proper arcs, vacuously. -/
theorem CellPocketWalkRefutedBelowInput.toProperArcs {D : RelGenSet G Lambda} {lambda c mu : ℝ}
    {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (h : CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W) :
    CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W :=
  P06Bypass.properArcsBelowInput_of_refuted h

end Input

/-- **The refuted walk binder below the inductive bound, beyond thresholds**: the landed
`P06Bypass.CellPocketWalkRefutedBelowSectionStatement`. -/
abbrev CellPocketWalkRefutedBelowSectionStatement : Prop :=
  P06Bypass.CellPocketWalkRefutedBelowSectionStatement.{u, w, v}

/-- The refuted section binder gives the below proper arcs, at the same thresholds. -/
theorem properArcsBelowSection_of_refuted
    (h : CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} :=
  P06Bypass.properArcsBelowSection_of_refuted h

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive.CellPocketWalkRefutedBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive.CellPocketWalkRefutedBelowInput.toProperArcs
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive.CellPocketWalkRefutedBelowSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive.properArcsBelowSection_of_refuted
