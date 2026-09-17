import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketMultipleEdgeCopyBelow
import GroupApproximation.Meta.AxiomGuard

/-!
# The refuted walk binder, as consumed by binder 5 below the bound

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

Binder 5 below the inductive bound (`copyRegion_of_offSideWalkSectionPinchBelow`,
`Common/CellStepBelow.lean`) calls the proper-arcs residual `hproper` on the walk binder of
`CellPocketWalkProperArcsBelowInput` (`Estimating/OsinPocketMultipleEdgeCopyBelow.lean`).  Route 3
of P07 (`P07LakeExclusion.proof_of_innerTwoArcLong`) runs `exfalso` on exactly that binder.  So the
binder is contradictory, and binder 5 needs neither the pinch (residual 06) nor the Euler residual.

This module states the refuted form of the binder.  Lane gl-p06-01 owns the same interface in the
namespace `P06Bypass`; it was not on disk when this lane was written.  To avoid a duplicate
declaration when both modules are imported together, the interface is stated here in the
sub-namespace `P06Bypass.BinderFive`.  The bodies are verbatim the bodies requested for gl-p06-01,
so a term of either version has the type of the other by unfolding.

* `BinderFive.CellPocketWalkRefutedBelowInput`: the binder of `CellPocketWalkProperArcsBelowInput`
  with conclusion `False`.
* `BinderFive.CellPocketWalkRefutedBelowSectionStatement`: the same beyond the thresholds of
  `CellPocketWalkProperArcsBelowSectionStatement`.
* `BinderFive.CellPocketWalkRefutedBelowInput.toProperArcs` and
  `BinderFive.properArcsBelowSection_of_refuted`: the refuted binder gives the proper arcs.

## Why the interface is true

`P07LakeExclusion.proof_of_innerTwoArcLong` derives `False` on this binder from the long-word inner
two-arc pocket residual.  Its last step is `Piece06.false_of_lakeFillTwoArcExit`, a strictly
smaller relator-cell count through `OsinMultipleEdgeCut.false_of_below`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive

universe u w v

open Embedded HullSC WordMetric SimpleClosedWalkSides

section Input

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The walk binder of the below proper arcs is refuted.**  The hypotheses of
`CellPocketWalkProperArcsBelowInput`, with conclusion `False`: a cell pocket walk of two distinct
selected regions joining two distinct cells, noncrossing, with the exterior off its side, over a
least-area diagram where clause (b) of Lemma 9.7 holds below its number of relator cells, does not
exist. -/
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

/-- The refuted binder gives the below proper arcs, vacuously. -/
theorem CellPocketWalkRefutedBelowInput.toProperArcs {D : RelGenSet G Lambda} {lambda c mu : ℝ}
    {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (h : CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W) :
    CellPocketWalkProperArcsBelowInput.{u, w, v} D lambda c mu eps W :=
  fun Delta cuts hlea hbelow S _ _ _ _ ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
    hoff => (h Delta cuts hlea hbelow S ha hb hab hij hai hbi hclean K hfirst hsecond h₁ h₂ hw
      hoff).elim

end Input

/-- **The refuted walk binder below the inductive bound, beyond thresholds**, with the thresholds
of `CellPocketWalkProperArcsBelowSectionStatement`. -/
def CellPocketWalkRefutedBelowSectionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c mu : ℝ, 0 < lambda → lambda ≤ 1 → 0 ≤ c → 0 < mu → mu ≤ 1 / 16 →
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (RelLetter G Lambda))),
            OsinCCondition D W eps mu lambda c rho →
              CellPocketWalkRefutedBelowInput.{u, w, v} D lambda c mu eps W

/-- The refuted section binder gives the below proper arcs, at the same thresholds. -/
theorem properArcsBelowSection_of_refuted
    (h : CellPocketWalkRefutedBelowSectionStatement.{u, w, v}) :
    CellPocketWalkProperArcsBelowSectionStatement.{u, w, v} := by
  intro G _ Lambda D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  obtain ⟨eps0, heps0⟩ := h D hhyp lambda c mu hlambda hlambda1 hc hmu hmu16
  refine ⟨eps0, fun eps heps => ?_⟩
  obtain ⟨rho0, hrho0, hrho⟩ := heps0 eps heps
  exact ⟨rho0, hrho0, fun rho hrho' W hW => (hrho rho hrho' W hW).toProperArcs⟩

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive.CellPocketWalkRefutedBelowInput
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive.CellPocketWalkRefutedBelowInput.toProperArcs
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive.CellPocketWalkRefutedBelowSectionStatement
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06Bypass.BinderFive.properArcsBelowSection_of_refuted
