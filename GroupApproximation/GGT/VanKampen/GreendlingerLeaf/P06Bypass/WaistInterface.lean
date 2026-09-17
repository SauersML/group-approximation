import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.InnerTwoArcLong
import GroupApproximation.Meta.AxiomGuard

/-!
# The refuted walk binder and the two bypass interfaces (lane gl-p06-03, interfaces)

Lane gl-p06-03 retires residual 06 (`CellPocketOuterPinchStepSectionDistinctBelowStatement`) from
the Below Greendlinger waist.  In `copyRegion_of_offSideWalkSectionPinchBelow`
(`GreendlingerLeaf/Common/CellStepBelow`, :203) the proper-arcs residual `hproper` is applied, at
:259, to exactly the walk binder that the P07 route-3 argument refutes
(`P07LakeExclusion.proof_of_innerTwoArcLong`, `InnerTwoArc.lean`:86, runs `exfalso` right after the
intro).  So binder 5 below the bound needs no pinch once that binder is refuted.

The upstream lanes gl-p06-01 (the refuted binder, namespace `P06Bypass`) and gl-p06-02 (binder 5
from it) ran in parallel with this lane.  Their interfaces were stated here, in the sub-namespace
`P06Bypass.Waist` so that no name collides with theirs.  The lane endpoints (`WaistFour.lean`,
`WaistFrontier.lean`) now use the landed `RefutedDef`, `RefutedCore` and `BinderFiveSection`, not
this module.  This module stays because `BinderFiveWaistBridge.lean` imports it:

* `CellPocketWalkRefutedBelowInput`, `CellPocketWalkRefutedBelowSectionStatement`: the binder of
  `CellPocketWalkProperArcsBelowInput` (`Estimating/OsinPocketMultipleEdgeCopyBelow`, :55) with
  conclusion `False`, at the thresholds of :107.  This is the lane gl-p06-01 shape verbatim.
* `BinderFiveOfRefutedStatement`: the lane gl-p06-02 theorem
  `P06Bypass.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`, as a Prop.
* `RefutedOfInnerTwoArcLongStatement`: the lane gl-p06-01 theorem
  `P06Bypass.refutedBelowSection_of_innerTwoArcLong`, as a Prop.

Proved here:

* `properArcsBelowInput_of_refuted`, `properArcsBelowSection_of_refuted`: a refuted binder gives the
  proper arcs (`False.elim`), at the same thresholds.
* `refutedBelowSection_of_innerPocketEnclosed_of_long`: the enclosed variant, through the on-disk
  `P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed` (`InnerTwoArcLong.lean`:85).

## Truth check

* The refuted binder is true beyond the thresholds `eps0 = 0`, `rho0 = max 2 rho1`
  (`SameCellSimplePocket.exists_rho_large`) whenever `CellPocketInnerTwoArcLongStatement` holds:
  the body of `proof_of_innerTwoArcLong` derives `False` from exactly these hypotheses.
* `BinderFiveOfRefutedStatement` is true: in `multipleEdgePocketRegionCopyBelowInput_of_…` the only
  walk consumed is one with `hw`, `hoff`, `hlea`, `hbelow` on the section diagram of the original
  `Delta`, which is the refuted binder, so that branch closes by `False.elim` with the thresholds
  passed through (no `max`).

## Manuscript status

Infrastructure for `thm:hull` (Osin's Lemma 4.4 at least-area diagrams, through Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The cell pocket walk with the exterior off its side is refuted below the inductive bound**:
the binder of `CellPocketWalkProperArcsBelowInput` with conclusion `False` (lane gl-p06-01
interface). -/
def CellPocketWalkRefutedBelowInput (D : RelGenSet G Lambda) (lambda c mu : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea → OsinLemma97Below.{u, w, v} D lambda c mu eps W Delta.rCellCount →
      ∀ (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
        {i j : Fin S.diagram.rCellCount} {a b : RegionCandidate D eps S.diagram},
        a ∈ S.family → b ∈ S.family → a ≠ b → i ≠ j → a.JoinsCells i j → b.JoinsCells i j →
          CellPocketWalk.CopyClean a b i j →
          ∀ K : CellPocketWalk D eps S.diagram i j,
            K.firstSide = b.sideFrom j → K.secondSide = a.sideFrom i →
            (∃ G₁ : CyclicArc (cellDarts S.diagram i),
              K.firstArc.darts = a.cellArcList i ++ G₁.darts ++ b.cellArcList i) →
            (∃ G₂ : CyclicArc (cellDarts S.diagram j),
              K.secondArc.darts = b.cellArcList j ++ G₂.darts ++ a.cellArcList j) →
            IsNoncrossingClosedWalk S.diagram.toCombMap K.walk →
            S.diagram.outerFace ∉ sideFaces S.diagram.toCombMap K.walk →
              False

/-- A refuted walk binder gives the proper arcs, at fixed parameters. -/
theorem properArcsBelowInput_of_refuted {D : RelGenSet G Lambda} {lambda c mu : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (h : CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W) :
    CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W :=
  fun Delta cuts hlea hbelow S _ _ _ _ ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff =>
    (h Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw hoff).elim

end Input

/-- **The refuted walk binder below the inductive bound, beyond thresholds** (lane gl-p06-01
interface; thresholds as in `CellPocketWalkProperArcsBelowSectionStatement`). -/
def CellPocketWalkRefutedBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W

/-- A refuted walk binder beyond thresholds gives the proper arcs, at the same thresholds. -/
theorem properArcsBelowSection_of_refuted
    (h : CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps0, hEps⟩ := h D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hRho⟩ := hEps eps heps
  exact ⟨rho0, hrho0, fun rho hrho W hcondition =>
    properArcsBelowInput_of_refuted (hRho rho hrho W hcondition)⟩

/-- **Binder 5 below the bound from the refuted walk binder** (lane gl-p06-02 interface, the theorem
`P06Bypass.osinMultipleEdgePocketRegionCopyBelowSection_of_refuted`, as a Prop).  True: the pinch
of `copyRegion_of_offSideWalkSectionPinchBelow` sits behind the refuted binder. -/
def BinderFiveOfRefutedStatement : Prop :=
  CellPocketWalkRefutedBelowSectionStatement.{u, w, v} →
    OsinMultipleEdgePocketRegionCopyBelowSectionStatement.{u, w, v}

/-- **The refuted walk binder from the long inner two-arc Statement** (lane gl-p06-01 interface, the
theorem `P06Bypass.refutedBelowSection_of_innerTwoArcLong`, as a Prop).  True: it is the body of
`P07LakeExclusion.proof_of_innerTwoArcLong` without the `exfalso`. -/
def RefutedOfInnerTwoArcLongStatement : Prop :=
  P07LakeExclusion.CellPocketInnerTwoArcLongStatement.{u, w, v} →
    CellPocketWalkRefutedBelowSectionStatement.{u, w, v}

/-- The refuted walk binder from the enclosed inner pocket, through
`P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed`. -/
theorem refutedBelowSection_of_innerPocketEnclosed_of_long
    (hlong : RefutedOfInnerTwoArcLongStatement.{u, w, v})
    (h : P07LakeExclusion.InnerPocketEnclosedTwoArcStatement.{u, w, v}) :
    CellPocketWalkRefutedBelowSectionStatement.{u, w, v} :=
  hlong (P07LakeExclusion.innerTwoArcLong_of_innerPocketEnclosed h)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.CellPocketWalkRefutedBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.properArcsBelowInput_of_refuted
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.CellPocketWalkRefutedBelowSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.properArcsBelowSection_of_refuted
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.BinderFiveOfRefutedStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.RefutedOfInnerTwoArcLongStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.Waist.refutedBelowSection_of_innerPocketEnclosed_of_long
