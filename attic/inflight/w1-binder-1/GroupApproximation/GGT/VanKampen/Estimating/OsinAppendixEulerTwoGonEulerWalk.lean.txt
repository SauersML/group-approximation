import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonInnerAssembly
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketKeptCellSection
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-gon pocket walk through Euler equalities

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`TwoGonInnerFollowsWalkInput` (`Estimating/OsinAppendixEulerTwoGonInnerAssembly`) asks that the
inner cycle of the noncrossing pocket walk follows its boundary.  A walk touching itself once in
each way has neither boundary cycle following (`OsinPocketMixedTouchModel`), but both of its
reclosings keep the Euler characteristic of the map, and `PocketRegion.ofNoncrossingClosedWalkEuler`
builds a pocket region from those two equalities alone.  This module states the residual with the
Euler equalities in place of inner following.

* `TwoGonEulerWalkInput`: for the labels of a two-gon, a noncrossing walk equal to the decomposition
  `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` whose two reclosings keep the
  Euler characteristic, the four span inclusions, and the printed arc bounds.
* `twoGonEulerWalkInput_of_innerFollowsWalk`: inner following gives the Euler equalities
  (`IsNoncrossingClosedWalk.eulers_of_eitherFollows`), so the Euler form is the weaker residual.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides Surgery.MapCollapse

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The two-gon pocket walk with Euler equalities.**  For the labels of a two-gon of `phiMapO`
with no corner in its gap and no relator cell, exterior regions `a ≠ b` of one cell `i` to one
section `j`, target arc of `a` first:
* the walk `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` is noncrossing, and
  both of its reclosings keep the Euler characteristic of the map;
* the source arc contains the source arcs of `a` and `b`, and the target arc contains their target
  arcs;
* the source arc is at least as long as the source arcs of `a` and `b` together;
* the target arc runs from the start of the target arc of `a` to the end of that of `b`. -/
def TwoGonEulerWalkInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
    (W : Set (List (RelLetter G Lambda))) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W) (cuts : SectionCuts D lambda c Delta.boundaryWord),
    Delta.LeastArea →
      ∀ S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts,
        S.NoLoops → S.NoMultipleEdges →
          ∀ a₀ ∈ S.family, a₀.2.target = none →
            ∀ (P : RegionCandidate.ExtPhiData S.family
                (RegionCandidate.linkedComponentO S.family a₀))
              (f : (RegionCandidate.phiMapO S.family
                (RegionCandidate.linkedComponentO S.family a₀)).Face),
              (RegionCandidate.phiSubdividedMultigraphO P).IsTwoGon f →
              ¬RegionCandidate.GapAtOHoldsCorner cuts S.family
                (RegionCandidate.linkedComponentO S.family a₀) f →
              ¬RegionCandidate.HoldsCellO S.family
                (RegionCandidate.linkedComponentO S.family a₀) f →
              ∀ (i : Fin S.diagram.rCellCount) (j : Fin cuts.count),
                ∀ a ∈ RegionCandidate.exteriorAt S.family i,
                  ∀ b ∈ RegionCandidate.exteriorAt S.family i, a ≠ b →
                    RegionCandidate.TargetsSectionIndex cuts j a →
                      RegionCandidate.TargetsSectionIndex cuts j b →
                        a.2.targetArc.start.1 + a.2.targetArc.length ≤
                          b.2.targetArc.start.1 →
                          ∃ (source : CyclicArc (cellDarts S.diagram i))
                            (target : CyclicArc (targetDarts S.diagram none))
                            (hw : IsNoncrossingClosedWalk S.diagram.toCombMap
                              (source.reverseDarts ++ a.2.rightSide ++ target.darts ++
                                b.2.leftSide)),
                            ((reclosedMap S.diagram.toCombMap
                                (sideFaces S.diagram.toCombMap
                                  (source.reverseDarts ++ a.2.rightSide ++ target.darts ++
                                    b.2.leftSide))
                                (hw.innerCycle S.diagram.planar)).eulerCharacteristic =
                                S.diagram.toCombMap.eulerCharacteristic ∧
                              (reclosedMap S.diagram.toCombMap
                                  (sideOutside S.diagram.toCombMap
                                    (source.reverseDarts ++ a.2.rightSide ++ target.darts ++
                                      b.2.leftSide))
                                  (hw.outerCycle S.diagram.planar)).eulerCharacteristic =
                                S.diagram.toCombMap.eulerCharacteristic) ∧
                              (∀ d ∈ a.2.sourceArc.darts, d ∈ source.darts) ∧
                              (∀ d ∈ b.2.sourceArc.darts, d ∈ source.darts) ∧
                              (∀ d ∈ a.2.targetArc.darts, d ∈ target.darts) ∧
                              (∀ d ∈ b.2.targetArc.darts, d ∈ target.darts) ∧
                              a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length ∧
                              target.start.1 = a.2.targetArc.start.1 ∧
                              target.start.1 + target.length =
                                b.2.targetArc.start.1 + b.2.targetArc.length ∧
                              a.2.targetArc.length + b.2.targetArc.length ≤ target.length

/-- **The Euler form is the weaker residual.**  An inner-following pocket walk keeps the Euler
characteristic under both reclosings. -/
theorem twoGonEulerWalkInput_of_innerFollowsWalk {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (hwalk : TwoGonInnerFollowsWalkInput.{u, w, v} D lambda c eps W) :
    TwoGonEulerWalkInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell i j a ha b hb hab hja hjb
    horder
  obtain ⟨source, target, hw, hin, hrest⟩ :=
    hwalk Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell i j a ha b hb hab hja hjb
      horder
  exact ⟨source, target, hw, hw.eulers_of_eitherFollows S.diagram.planar (Or.inr hin), hrest⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonEulerWalkInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonEulerWalkInput_of_innerFollowsWalk
