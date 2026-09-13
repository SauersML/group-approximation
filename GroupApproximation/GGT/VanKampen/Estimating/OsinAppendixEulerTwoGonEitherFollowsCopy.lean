import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonEitherFollows
import GroupApproximation.Meta.AxiomGuard

/-!
# C6′ through a noncrossing pocket on another distinguished family

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

The pocket walk of the two regions of a two-gon need not be noncrossing on the given diagram.
- An outer spur or a shared edge can repeat a dart, or use an edge in both directions.
- The planned route passes to a globally distinguished family `S'` over the same diagram `Δ` and
  the same section cuts: an O-equivalent copy such as the one given by
  `OuterSpurThickeningStatement`.
- There the edge conditions `PocketWalk.CopyClean` make the walk noncrossing
  (`PocketWalk.isNoncrossingClosedWalk_of_copyClean`).
- A contradiction on `S'` is a contradiction, so C6′ holds as soon as some such `S'` carries two
  exterior regions of one cell to one section with a noncrossing pocket.

* `GloballyDistinguishedSectionFamily.false_of_eitherFollowsPocket`: on any globally distinguished
  family of a least-area diagram, two exterior regions of one cell to one section whose pocket walk
  is noncrossing, with its outer or inner cycle following, holding both regions, no relator cell
  and no other selected region, give a contradiction.
* `TwoGonEitherFollowsCopyInput`: for the labels of a two-gon, such a pocket on some globally
  distinguished family over the same diagram and cuts.
* `twoGonHoldsInput_of_eitherFollowsCopy`: `TwoGonHoldsInput` from it.
* `twoGonEitherFollowsCopyInput_of_pocketInput`: taking `S' = S` recovers
  `TwoGonEitherFollowsPocketInput`, so the copy form is the weaker residual.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(a)); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **A noncrossing pocket of two exterior regions refutes the choice of the family.**  Let `S` be
a globally distinguished section family of a least-area diagram, `a ≠ b` exterior regions of the
cell `i` to the section `j`, and let the walk `source.reverseDarts ++ a.rightSide ++ target.darts ++
b.leftSide` be noncrossing with its outer or its inner cycle following its boundary.  Suppose the
faces of `a` and `b` lie on its side, and no relator cell and no other selected region does.
Suppose also that the source arc spans the source arcs of `a` and `b`, and the target arc runs from
the start of the target arc of `a` to the end of that of `b`.  Then there is a contradiction. -/
theorem GloballyDistinguishedSectionFamily.false_of_eitherFollowsPocket
    (hinner : PocketRegionOfInnerFollowsStatement.{u, w, v})
    {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    (hlea : Delta.LeastArea)
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b)
    (source : CyclicArc (cellDarts S.diagram i))
    (target : CyclicArc (targetDarts S.diagram none))
    (hw : IsNoncrossingClosedWalk S.diagram.toCombMap
      (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide))
    (hfollow : (hw.outerCycle S.diagram.planar).FollowsBoundary ∨
      (hw.innerCycle S.diagram.planar).FollowsBoundary)
    (hsubA : a.1 ⊆ SimpleClosedWalkSides.sideFaces S.diagram.toCombMap
      (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide))
    (hsubB : b.1 ⊆ SimpleClosedWalkSides.sideFaces S.diagram.toCombMap
      (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide))
    (hcells : ∀ C ∈ S.diagram.relatorCells, C.face ∉
      SimpleClosedWalkSides.sideFaces S.diagram.toCombMap
        (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide))
    (hothers : ∀ x ∈ S.family, x ≠ a → x ≠ b → Disjoint x.1
      (SimpleClosedWalkSides.sideFaces S.diagram.toCombMap
        (source.reverseDarts ++ a.2.rightSide ++ target.darts ++ b.2.leftSide)))
    (hsource : a.2.sourceArc.length + b.2.sourceArc.length ≤ source.length)
    (hstart : target.start.1 = a.2.targetArc.start.1)
    (hend : target.start.1 + target.length = b.2.targetArc.start.1 + b.2.targetArc.length)
    (htarget : a.2.targetArc.length + b.2.targetArc.length ≤ target.length) : False := by
  obtain ⟨-, hnd⟩ := S.nondegenerate _ (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
  have hpos : 0 < target.length := by omega
  have hout := outerFace_not_mem_sideFaces_of_target_mem hw target hpos
    (fun _ hd => List.mem_append_left _ (List.mem_append_right _ hd))
  rcases hfollow with hfollows | hin
  · have heuler := hw.reclosed_euler S.diagram.planar hfollows
    exact emptyTwoGonInput_holds D lambda c eps W Delta cuts hlea S i j a ha b hb hab hja hjb
      (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler) hsubA hsubB hcells hothers
      source target hsource hstart hend htarget
      (PocketRegion.ofNoncrossingClosedWalk_invDarts_outer hw hout hfollows heuler)
  · obtain ⟨Q, hQfaces, hQouter⟩ := hinner hw hout hin
    exact emptyTwoGonInput_holds D lambda c eps W Delta cuts hlea S i j a ha b hb hab hja hjb
      Q (hQfaces ▸ hsubA) (hQfaces ▸ hsubB) (hQfaces ▸ hcells) (hQfaces ▸ hothers)
      source target hsource hstart hend htarget hQouter

/-- **The noncrossing pocket of a two-gon, on another distinguished family.**  Take the binders of
`TwoGonHoldsInput` and the labels of the two-gon given by `exists_twoGonLabels`.  Then some globally
distinguished section family `S'` over the same diagram and section cuts carries exterior regions
`a' ≠ b'` of a cell `i'` to a section `j'`.  Their pocket walk is noncrossing, with its outer or inner
cycle following its boundary.  The faces of `a'` and `b'` lie on its side, and no relator cell and no
other selected region of `S'` does.  The source arc spans the source arcs of `a'` and `b'`, and the
target arc runs from the start of the target arc of `a'` to the end of that of `b'`. -/
def TwoGonEitherFollowsCopyInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
                          ∃ (S' : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
                            (i' : Fin S'.diagram.rCellCount) (j' : Fin cuts.count)
                            (a' b' : RegionCandidate D eps S'.diagram)
                            (source : CyclicArc (cellDarts S'.diagram i'))
                            (target : CyclicArc (targetDarts S'.diagram none))
                            (hw : IsNoncrossingClosedWalk S'.diagram.toCombMap
                              (source.reverseDarts ++ a'.2.rightSide ++ target.darts ++
                                b'.2.leftSide)),
                            a' ∈ RegionCandidate.exteriorAt S'.family i' ∧
                              b' ∈ RegionCandidate.exteriorAt S'.family i' ∧ a' ≠ b' ∧
                              RegionCandidate.TargetsSectionIndex cuts j' a' ∧
                              RegionCandidate.TargetsSectionIndex cuts j' b' ∧
                              ((hw.outerCycle S'.diagram.planar).FollowsBoundary ∨
                                (hw.innerCycle S'.diagram.planar).FollowsBoundary) ∧
                              a'.1 ⊆ SimpleClosedWalkSides.sideFaces S'.diagram.toCombMap
                                (source.reverseDarts ++ a'.2.rightSide ++ target.darts ++
                                  b'.2.leftSide) ∧
                              b'.1 ⊆ SimpleClosedWalkSides.sideFaces S'.diagram.toCombMap
                                (source.reverseDarts ++ a'.2.rightSide ++ target.darts ++
                                  b'.2.leftSide) ∧
                              (∀ C ∈ S'.diagram.relatorCells, C.face ∉
                                SimpleClosedWalkSides.sideFaces S'.diagram.toCombMap
                                  (source.reverseDarts ++ a'.2.rightSide ++ target.darts ++
                                    b'.2.leftSide)) ∧
                              (∀ x ∈ S'.family, x ≠ a' → x ≠ b' → Disjoint x.1
                                (SimpleClosedWalkSides.sideFaces S'.diagram.toCombMap
                                  (source.reverseDarts ++ a'.2.rightSide ++ target.darts ++
                                    b'.2.leftSide))) ∧
                              a'.2.sourceArc.length + b'.2.sourceArc.length ≤ source.length ∧
                              target.start.1 = a'.2.targetArc.start.1 ∧
                              target.start.1 + target.length =
                                b'.2.targetArc.start.1 + b'.2.targetArc.length ∧
                              a'.2.targetArc.length + b'.2.targetArc.length ≤ target.length

/-- **C6′ from a noncrossing pocket on another distinguished family.**  The labels of the two-gon
feed `TwoGonEitherFollowsCopyInput`, whose pocket on `S'` is refuted by
`GloballyDistinguishedSectionFamily.false_of_eitherFollowsPocket`. -/
theorem twoGonHoldsInput_of_eitherFollowsCopy {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hinner : PocketRegionOfInnerFollowsStatement.{u, w, v})
    (hcopy : TwoGonEitherFollowsCopyInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  obtain ⟨y, -, -, -, -, j, hya, hyb, hab, hja, hjb, horder⟩ :=
    RegionCandidate.exists_twoGonLabels S hmulti P hf hcorner
  obtain ⟨S', i', j', a', b', source, target, hw, ha', hb', hab', hja', hjb', hfollow, hsubA,
      hsubB, hcells, hothers, hsource, hstart, hend, htarget⟩ :=
    hcopy Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell _ j _ hya _ hyb hab
      hja hjb horder
  exact S'.false_of_eitherFollowsPocket hinner hlea ha' hb' hab' hja' hjb' source target hw
    hfollow hsubA hsubB hcells hothers hsource hstart hend htarget

/-- **The copy form is the weaker residual:** taking `S' = S`, `TwoGonEitherFollowsPocketInput`
gives `TwoGonEitherFollowsCopyInput`. -/
theorem twoGonEitherFollowsCopyInput_of_pocketInput {D : RelGenSet G Lambda} {lambda c : ℝ}
    {eps : ℕ} {W : Set (List (RelLetter G Lambda))}
    (hpocket : TwoGonEitherFollowsPocketInput.{u, w, v} D lambda c eps W) :
    TwoGonEitherFollowsCopyInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell i j a ha b hb hab hja hjb
    horder
  obtain ⟨source, target, walk, hw, hwalk, hfollow, hsubA, hsubB, hcells, hothers, hsource,
      hstart, hend, htarget⟩ :=
    hpocket Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell i j a ha b hb hab
      hja hjb horder
  subst hwalk
  exact ⟨S, i, j, a, b, source, target, hw, ha, hb, hab, hja, hjb, hfollow, hsubA, hsubB, hcells,
    hothers, hsource, hstart, hend, htarget⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.false_of_eitherFollowsPocket
#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonEitherFollowsCopyInput
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_eitherFollowsCopy
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonEitherFollowsCopyInput_of_pocketInput
