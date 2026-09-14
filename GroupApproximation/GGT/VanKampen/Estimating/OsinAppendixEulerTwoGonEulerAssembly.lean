import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonPocketFacesEuler
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonEulerWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# C6′ for a two-gon pocket through Euler equalities, without a connected walk

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`"; and the proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ′_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

`twoGonHoldsInput_of_innerFollowsWalk` (`Estimating/OsinAppendixEulerTwoGonInnerAssembly`) uses the
inner following of the pocket walk twice: for the field `connected` of the walk hypotheses, and for
the disc region of the side.  A walk touching itself once in each way keeps neither
(`OsinPocketMixedTouchModel`), but both of its reclosings keep the Euler characteristic.  This
module replaces both uses.

* The pocket region comes from the two Euler equalities
  (`PocketRegion.ofNoncrossingClosedWalkEuler`, lane `w1-binder-6`), and its inner disc region
  (`Surgery.InnerDiscRegion.ofPocketRegion`) has the decomposition as its cycle.
* `hno` and `havoid` come from the side hypotheses and a per-walk-dart base
  (`Estimating/OsinAppendixEulerTwoGonPocketFacesEuler`).  The darts of the sides of `a` and `b`
  and those across their arcs lie on faces of `a` or `b`.

* `TwoGonEulerGapInput`: for the labels of a two-gon and a pocket walk of the shape of
  `TwoGonEulerWalkInput`, every dart across the source span outside the source arcs of `a` and `b`,
  and every dart of the target span outside their target arcs, lies on a face of the pocket of the
  face class of the two-gon (named residual).  Hand argument, not built: the gap darts are not
  retained, since the two-gon face turns at cell `i` and at the outer vertex with no other region of
  the component in its corner, so the face class runs along the gaps (`faceClassO_of_isChain`) from
  the first source dart of `b` and the reversed first target dart of `a`, and
  `ExtPhiData.twoGonPocketFace_of_faceClassO` applies.
* `twoGonHoldsInput_of_eulerWalk`: `TwoGonHoldsInput` from `TwoGonEulerWalkInput` and
  `TwoGonEulerGapInput`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121 at origin/main 68481e4d7, through Osin's Lemma 9.7(a));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The gap darts of a two-gon pocket walk lie on faces of the pocket** (named residual).  For
the labels of a two-gon of `phiMapO` with no corner in its gap and no relator cell, with outer cell
dart `y`, its region `a` and the region `b` two steps on, and a noncrossing walk
`source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` whose spans hold the arcs of
`a` and `b` with the printed bounds: every dart across a source dart outside the source arcs of `a`
and `b`, and every target dart outside their target arcs, lies on a face of the pocket of the face
class of `y`. -/
def TwoGonEulerGapInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
              ∀ (y : (RegionCandidate.phiMapO S.family
                  (RegionCandidate.linkedComponentO S.family a₀)).Dart)
                (a b : RegionCandidate D eps S.diagram),
                RegionCandidate.phiCellSideO y = true →
                (RegionCandidate.phiMapO S.family
                  (RegionCandidate.linkedComponentO S.family a₀)).faceOf y = f →
                RegionCandidate.sideCellO (RegionCandidate.phiRegionO y)
                  (RegionCandidate.phiSideO y) = none →
                RegionCandidate.phiRegionO y = a →
                RegionCandidate.phiRegionO ((RegionCandidate.phiMapO S.family
                    (RegionCandidate.linkedComponentO S.family a₀)).facePerm
                  ((RegionCandidate.phiMapO S.family
                    (RegionCandidate.linkedComponentO S.family a₀)).facePerm y)) = b →
                ∀ (source : CyclicArc (cellDarts S.diagram a.2.source))
                  (target : CyclicArc (targetDarts S.diagram none)),
                  IsNoncrossingClosedWalk S.diagram.toCombMap
                    (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide) →
                  (∀ d ∈ a.2.sourceArc.darts, d ∈ source.darts) →
                  (∀ d ∈ b.2.sourceArc.darts, d ∈ source.darts) →
                  (∀ d ∈ a.2.targetArc.darts, d ∈ target.darts) →
                  (∀ d ∈ b.2.targetArc.darts, d ∈ target.darts) →
                  a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length →
                  target.start.1 = a.2.targetArc.start.1 →
                  target.start.1 + target.length =
                    b.2.targetArc.start.1 + b.2.targetArc.length →
                  (∀ p ∈ source.darts, p ∉ a.2.sourceArc.darts → p ∉ b.2.sourceArc.darts →
                    RegionCandidate.TwoGonPocketFace S.family
                      (RegionCandidate.linkedComponentO S.family a₀) y.1 a b
                      (S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha p))) ∧
                    ∀ d ∈ target.darts, d ∉ a.2.targetArc.darts → d ∉ b.2.targetArc.darts →
                      RegionCandidate.TwoGonPocketFace S.family
                        (RegionCandidate.linkedComponentO S.family a₀) y.1 a b
                        (S.diagram.toCombMap.faceOf d)

/-- **C6′ from an Euler pocket walk.**  The labels of the two-gon come with its outer cell dart
`y`.
* `twoGonClassHyp_of_linkedComponent` gives the class hypotheses at `y`.
* The side hypotheses come from `twoGonWalk_left_side`, `twoGonWalk_right_side`, and the outer and
  cell lemmas of the spans.
* The residual gives the gap darts, and `twoGonPocketFace_of_mem_decomposition` the per-walk-dart
  base, so `hno` and `havoid` hold without `connected`.
* The side is the inner disc region of `PocketRegion.ofNoncrossingClosedWalkEuler`.  Its cycle is
  the decomposition itself, so `false_of_mergeDisc` gives the contradiction. -/
theorem twoGonHoldsInput_of_eulerWalk {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hwalk : TwoGonEulerWalkInput.{u, w, v} D lambda c eps W)
    (hgap : TwoGonEulerGapInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  obtain ⟨y, hy, hyf, hnone, h4, j, hya, hyb, hab, hja, hjb, horder⟩ :=
    RegionCandidate.exists_twoGonLabels S hmulti P hf hcorner
  obtain ⟨source, target, hw, heuler, hsrcA, hsrcB, htgtA, htgtB, hsource, hstart, hend,
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
  obtain ⟨hgapS, hgapT⟩ := hgap Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
    y _ _ hy hyf hnone rfl rfl source target hw hsrcA hsrcB htgtA htgtB hsource hstart hend
  have hout := outerFace_not_mem_sideFaces_of_target_mem hw target hposT hsubT
  have Hs := RegionCandidate.TwoGonWalkSideHyp.mk
    (RegionCandidate.twoGonWalk_left_side source target H.target_left hsrcA htgtA)
    (RegionCandidate.twoGonWalk_right_side source target H.target_right hsrcB htgtB)
    hout (cellFace_not_mem_sideFaces_of_source_mem hw source hposS hsubS)
  have hbase := RegionCandidate.twoGonPocketFace_of_mem_decomposition (x := y.1) source target
    H.target_left H.target_right hgapS hgapT
  have hno := P.cell_face_not_mem_sideFaces_of_twoGon_of_base H Hs hbase
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
  exact S.false_of_mergeDisc hya hyb hab hja hjb
    (Surgery.InnerDiscRegion.ofPocketRegion
      (PocketRegion.ofNoncrossingClosedWalkEuler hw hout heuler.1 heuler.2) hcells)
    source target (k := 0) (List.rotate_zero _)
    (fun _ hx hxa hxb => P.disjoint_sideFaces_of_twoGon_of_base H Hs hbase hx hxa hxb)
    hsource hstart hend htarget

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonEulerGapInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_eulerWalk
