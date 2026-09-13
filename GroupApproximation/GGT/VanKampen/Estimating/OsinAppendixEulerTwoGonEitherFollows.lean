import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonNoncrossingRoute
import GroupApproximation.Meta.AxiomGuard

/-!
# C6′ from a noncrossing pocket walk with either boundary cycle following

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`"; and the proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ′_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

`twoGonHoldsInput_of_noncrossingPocket` (`Estimating/OsinAppendixEulerTwoGonNoncrossingRoute`)
proves C6′ from a noncrossing pocket walk whose outer cycle follows its boundary.  A pinched pocket
comes in two configurations:
- in Configuration A (the pinched two-gon) the outer cycle follows;
- in Configuration B (the lake) the inner cycle follows and the outer cycle does not
  (`OsinPocketLakeModel`).

In both, the complement of the pocket is still a disc region: reclosing it along the reversed walk
splits the pinch vertex.  So a pocket region exists either way.
- When the outer cycle follows, `PocketRegion.ofNoncrossingClosedWalk` builds it.
- When the inner cycle follows, the builder is `PocketRegionOfInnerFollowsStatement` (lane
  `ms-torsionfree`).  Its outer region should come from `reclosed_euler` on the reversed walk.

* `PocketRegionOfInnerFollowsStatement`: a noncrossing walk whose inner cycle follows, with the
  exterior face off its side, is the inverse complement cycle of a pocket region whose faces are its
  side.
* `TwoGonEitherFollowsPocketInput`: `TwoGonNoncrossingPocketInput` with the outer following clause
  replaced by "the outer cycle or the inner cycle follows its boundary".
* `twoGonHoldsInput_of_eitherFollows`: `TwoGonHoldsInput` from the two.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(a)); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

/-- **The pocket region of a noncrossing walk whose inner cycle follows** (lane `ms-torsionfree`).
Let `walk` be a noncrossing closed walk of a diagram whose inner cycle follows its boundary and
whose side does not hold the exterior face.  Then there is a pocket region whose faces are the side
of the walk and whose complement cycle, read backwards, is the walk.  This is the lake,
Configuration B, where `PocketRegion.ofNoncrossingClosedWalk` does not apply. -/
def PocketRegionOfInnerFollowsStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} {walk : List Delta.toCombMap.Dart}
    (hw : IsNoncrossingClosedWalk Delta.toCombMap walk),
    Delta.outerFace ∉ SimpleClosedWalkSides.sideFaces Delta.toCombMap walk →
    (hw.innerCycle Delta.planar).FollowsBoundary →
      ∃ P : PocketRegion Delta,
        P.faces = SimpleClosedWalkSides.sideFaces Delta.toCombMap walk ∧
          invDarts Delta P.outer.cycle = walk

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The noncrossing pocket of a two-gon of `Φ'_M`, with either boundary cycle following.**  Take
the binders of `TwoGonHoldsInput` and the labels of the two-gon given by `exists_twoGonLabels`:
exterior regions `a ≠ b` of the cell `i`, both targeting the section `j`, with the target arc of
`a` ending before that of `b` starts.  Then there are a source arc, a target arc and a noncrossing
walk `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide`.  Its outer cycle or its
inner cycle follows its boundary.  The faces of `a` and `b` lie on its side, and no relator cell and
no other selected region does.  The source arc is at least as long as the source arcs of `a` and `b`
together, and the target arc runs from the start of the target arc of `a` to the end of that of
`b`. -/
def TwoGonEitherFollowsPocketInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
                            (walk : List S.diagram.toCombMap.Dart)
                            (hw : IsNoncrossingClosedWalk S.diagram.toCombMap walk),
                            walk = source.reverseDarts ++ a.2.rightSide ++ target.darts ++
                                b.2.leftSide ∧
                              ((hw.outerCycle S.diagram.planar).FollowsBoundary ∨
                                (hw.innerCycle S.diagram.planar).FollowsBoundary) ∧
                              a.1 ⊆ SimpleClosedWalkSides.sideFaces S.diagram.toCombMap walk ∧
                              b.1 ⊆ SimpleClosedWalkSides.sideFaces S.diagram.toCombMap walk ∧
                              (∀ C ∈ S.diagram.relatorCells,
                                C.face ∉ SimpleClosedWalkSides.sideFaces S.diagram.toCombMap
                                  walk) ∧
                              (∀ x ∈ S.family, x ≠ a → x ≠ b →
                                Disjoint x.1
                                  (SimpleClosedWalkSides.sideFaces S.diagram.toCombMap walk)) ∧
                              a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length ∧
                              target.start.1 = a.2.targetArc.start.1 ∧
                              target.start.1 + target.length =
                                b.2.targetArc.start.1 + b.2.targetArc.length ∧
                              a.2.targetArc.length + b.2.targetArc.length ≤ target.length

/-- **C6′ from a noncrossing pocket with either boundary cycle following.**  The labels of the
two-gon give exterior regions `a ≠ b` of one cell to one section, the target arc of `a` first.
The exterior face is off the side of the pocket walk, from a dart of its target arc.
- If the outer cycle follows, `PocketRegion.ofNoncrossingClosedWalk` with the Euler equality of
  `reclosed_euler` is a pocket region.
- If the inner cycle follows, `PocketRegionOfInnerFollowsStatement` gives one.
Either way its faces are the side of the walk and its inverse complement cycle is the walk, and
`emptyTwoGonInput_holds` refutes it. -/
theorem twoGonHoldsInput_of_eitherFollows {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hinner : PocketRegionOfInnerFollowsStatement.{u, w, v})
    (hpocket : TwoGonEitherFollowsPocketInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  obtain ⟨y, -, -, -, -, j, hya, hyb, hab, hja, hjb, horder⟩ :=
    RegionCandidate.exists_twoGonLabels S hmulti P hf hcorner
  obtain ⟨source, target, walk, hw, hwalk, hfollow, hsubA, hsubB, hcells, hothers, hsource,
      hstart, hend, htarget⟩ :=
    hpocket Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell _ j _ hya _ hyb hab
      hja hjb horder
  subst hwalk
  obtain ⟨-, hnd⟩ := S.nondegenerate _ (Finset.mem_filter.mp (Finset.mem_filter.mp hya).1).1
  have hpos : 0 < target.length := by omega
  have hout := outerFace_not_mem_sideFaces_of_target_mem hw target hpos
    (fun _ hd => List.mem_append_left _ (List.mem_append_right _ hd))
  rcases hfollow with hfollows | hin
  · have heuler := hw.reclosed_euler S.diagram.planar hfollows
    exact emptyTwoGonInput_holds D lambda c eps W Delta cuts hlea S _ j _ hya _ hyb hab hja hjb
      (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler) hsubA hsubB hcells hothers
      source target hsource hstart hend htarget
      (PocketRegion.ofNoncrossingClosedWalk_invDarts_outer hw hout hfollows heuler)
  · obtain ⟨Q, hQfaces, hQouter⟩ := hinner hw hout hin
    exact emptyTwoGonInput_holds D lambda c eps W Delta cuts hlea S _ j _ hya _ hyb hab hja hjb
      Q (hQfaces ▸ hsubA) (hQfaces ▸ hsubB) (hQfaces ▸ hcells) (hQfaces ▸ hothers)
      source target hsource hstart hend htarget hQouter

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegionOfInnerFollowsStatement
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonEitherFollowsPocketInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_eitherFollows
