import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonClassHyp
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonWalkHypInner
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonMergeDisc
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionInnerFollows
import GroupApproximation.Meta.AxiomGuard

/-!
# C6′ for a two-gon pocket whose inner cycle follows, with `hno` and `havoid` proved

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`"; and the proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ′_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

The labels of a two-gon of `phiMapO` with no corner in its gap are exterior regions `a ≠ b` of one
cell to one section (`exists_twoGonLabels`).  Suppose the walk `source.reverseDarts ++ a.rightSide
++ target.darts ++ b.leftSide` is noncrossing, its inner cycle follows its boundary, and its arcs
span those of `a` and `b`.  Then every other piece of C6′ is a theorem:
* the hypotheses on the face class of the two-gon, `twoGonClassHyp_of_linkedComponent` (lane
  `w1-binder-1`);
* the hypotheses on the walk, `twoGonWalkHyp_of_innerFollows`, fed by `twoGonWalk_left_side`,
  `twoGonWalk_right_side` and `twoGonWalk_base` (lane `w1-binder-1`);
* no relator cell on the side of the walk, `ExtPhiData.cell_face_not_mem_sideFaces_of_twoGon`, and
  no other selected region meeting it, `ExtPhiData.disjoint_sideFaces_of_twoGon` (lane
  `debt-conditional`);
* the collapsible disc region of the side, `Surgery.InnerDiscRegion.ofNoncrossingClosedWalkInner`
  (lane `ms-torsionfree`);
* the contradiction, `GloballyDistinguishedSectionFamily.false_of_mergeDisc`.

* `TwoGonInnerFollowsWalkInput`: for the labels of a two-gon, a noncrossing walk equal to the
  decomposition whose inner cycle follows, the four span inclusions, and the printed arc bounds.
* `twoGonHoldsInput_of_innerFollowsWalk`: `TwoGonHoldsInput` from it.

When only the outer cycle follows (Configuration A, the pinched two-gon), the walk's darts need not
lie in one face class, so this assembly does not apply.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(a)); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The inner-following pocket walk of a two-gon of `Φ'_M`.**  Take the binders of
`TwoGonHoldsInput` and the labels of the two-gon given by `exists_twoGonLabels`: exterior regions
`a ≠ b` of the cell `i`, both targeting the section `j`, with the target arc of `a` ending before
that of `b` starts.  Then there are a source arc on the cell `i` and a target arc on the oriented
outer boundary such that:
* the walk `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` is noncrossing, and
  its inner cycle follows its boundary;
* the source arc contains the source arcs of `a` and `b`, and the target arc contains their target
  arcs;
* the source arc is at least as long as the source arcs of `a` and `b` together;
* the target arc runs from the start of the target arc of `a` to the end of that of `b`. -/
def TwoGonInnerFollowsWalkInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
                            (hw.innerCycle S.diagram.planar).FollowsBoundary ∧
                              (∀ d ∈ a.2.sourceArc.darts, d ∈ source.darts) ∧
                              (∀ d ∈ b.2.sourceArc.darts, d ∈ source.darts) ∧
                              (∀ d ∈ a.2.targetArc.darts, d ∈ target.darts) ∧
                              (∀ d ∈ b.2.targetArc.darts, d ∈ target.darts) ∧
                              a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length ∧
                              target.start.1 = a.2.targetArc.start.1 ∧
                              target.start.1 + target.length =
                                b.2.targetArc.start.1 + b.2.targetArc.length ∧
                              a.2.targetArc.length + b.2.targetArc.length ≤ target.length

/-- **C6′ from an inner-following pocket walk.**  The labels of the two-gon come with its outer cell
dart `y`.
* `twoGonClassHyp_of_linkedComponent` gives the class hypotheses at `y`.
* The walk hypotheses come from `twoGonWalkHyp_of_innerFollows`, whose region-reading fields are
  `twoGonWalk_left_side`, `twoGonWalk_right_side` and `twoGonWalk_base`.
* debt-conditional's theorems then put no relator cell and no other selected region on the side of
  the walk. The face class meets only end cells, because the two-gon holds no relator cell.
* The side is the disc region `InnerDiscRegion.ofNoncrossingClosedWalkInner`. Its cycle is the
  decomposition itself, so `false_of_mergeDisc` gives the contradiction. -/
theorem twoGonHoldsInput_of_innerFollowsWalk {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hwalk : TwoGonInnerFollowsWalkInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  obtain ⟨y, hy, hyf, hnone, h4, j, hya, hyb, hab, hja, hjb, horder⟩ :=
    RegionCandidate.exists_twoGonLabels S hmulti P hf hcorner
  obtain ⟨source, target, hw, hin, hsrcA, hsrcB, htgtA, htgtB, hsource, hstart, hend,
      htarget⟩ :=
    hwalk Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell _ j _ hya _ hyb hab
      hja hjb horder
  have H := RegionCandidate.twoGonClassHyp_of_linkedComponent S P hcell hy hyf hnone h4 hyb
  have hnondegA := S.nondegenerate _ (Finset.mem_filter.mp (Finset.mem_filter.mp hya).1).1
  have hposS : 0 < source.length := by omega
  have hposT : 0 < target.length := by omega
  have hsubS : ∀ d ∈ source.reverseDarts, d ∈
      source.reverseDarts ++ (RegionCandidate.phiRegionO y).2.rightSide ++ target.darts ++
        (RegionCandidate.phiRegionO ((RegionCandidate.phiMapO S.family
          (RegionCandidate.linkedComponentO S.family a₀)).facePerm
            ((RegionCandidate.phiMapO S.family
              (RegionCandidate.linkedComponentO S.family a₀)).facePerm y))).2.leftSide :=
    fun _ hd => List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hd))
  have hsubT : ∀ d ∈ target.darts, d ∈
      source.reverseDarts ++ (RegionCandidate.phiRegionO y).2.rightSide ++ target.darts ++
        (RegionCandidate.phiRegionO ((RegionCandidate.phiMapO S.family
          (RegionCandidate.linkedComponentO S.family a₀)).facePerm
            ((RegionCandidate.phiMapO S.family
              (RegionCandidate.linkedComponentO S.family a₀)).facePerm y))).2.leftSide :=
    fun _ hd => List.mem_append_left _ (List.mem_append_right _ hd)
  have Hw := twoGonWalkHyp_of_innerFollows hw hin source hposS hsubS target hposT hsubT
    (RegionCandidate.twoGonWalk_left_side source target H.target_left hsrcA htgtA)
    (RegionCandidate.twoGonWalk_right_side source target H.target_right hsrcB htgtB)
    (RegionCandidate.twoGonWalk_base source target H.target_left hnondegA htgtA)
  have hno := P.cell_face_not_mem_sideFaces_of_twoGon H Hw
    (fun k v hv hface => by
      by_contra hk
      exact hcell ⟨k, hk, y, hyf, v, hv, hface⟩)
  have hcells : ∀ C ∈ S.diagram.relatorCells, C.face ∉ sideFaces S.diagram.toCombMap
      (source.reverseDarts ++ (RegionCandidate.phiRegionO y).2.rightSide ++ target.darts ++
        (RegionCandidate.phiRegionO ((RegionCandidate.phiMapO S.family
          (RegionCandidate.linkedComponentO S.family a₀)).facePerm
            ((RegionCandidate.phiMapO S.family
              (RegionCandidate.linkedComponentO S.family a₀)).facePerm y))).2.leftSide) := by
    intro C hC
    obtain ⟨n, rfl⟩ := List.mem_iff_get.mp hC
    exact hno n
  have hout := outerFace_not_mem_sideFaces_of_target_mem hw target hposT hsubT
  exact S.false_of_mergeDisc hya hyb hab hja hjb
    (Surgery.InnerDiscRegion.ofNoncrossingClosedWalkInner hw hout hin hcells) source target
    (k := 0) (List.rotate_zero _)
    (fun _ hx hxa hxb => P.disjoint_sideFaces_of_twoGon H Hw hx hxa hxb)
    hsource hstart hend htarget

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonInnerFollowsWalkInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_innerFollowsWalk
