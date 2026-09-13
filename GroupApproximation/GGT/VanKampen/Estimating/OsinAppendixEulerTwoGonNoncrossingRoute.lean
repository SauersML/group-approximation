import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerSmallFaces
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonLabels
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketDiscEmptyTwoGon
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegionNoncrossingWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketSectionFaceSet
import GroupApproximation.GGT.VanKampen.NoncrossingClosedWalkEuler
import GroupApproximation.Meta.AxiomGuard

/-!
# C6′ through the pocket region of a noncrossing walk

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`"; and the proof of Lemma 9.7(a): "otherwise one can include the
ε-contiguity subdiagrams corresponding to the edges `e` and `f` of `Φ′_M` into a single
ε-contiguity subdiagram in the obvious way, contrary to the definition of `M`."

`TwoGonHoldsInput` (C6′, `Estimating/OsinAppendixEulerSmallFaces.lean`) says that a two-gon of
`phiMapO` with no corner in its gap that holds no relator cell gives a contradiction.  This module
reduces it to one named geometric Prop, with no case split on whether the pocket walk is simple:
`emptyTwoGonInput_holds` collapses the pocket through its disc region and allows a pinched pocket,
and `PocketRegion.ofNoncrossingClosedWalk` builds the pocket region of a noncrossing walk.

* `TwoGonNoncrossingPocketInput`: for the labels of a two-gon, the walk
  `source.reverseDarts ++ a.rightSide ++ target.darts ++ b.leftSide` around the pocket is a
  noncrossing closed walk whose outer cycle follows its boundary; the faces of `a` and `b` lie on
  its side; no relator cell and no other selected region lies on its side; and its arcs span those
  of `a` and `b`.
* `outerFace_not_mem_sideFaces_of_target_mem`: the exterior face is off the side of a noncrossing
  walk that holds the darts of a nonempty arc of the oriented outer boundary.
* `twoGonHoldsInput_of_noncrossingPocket`: `TwoGonHoldsInput` from `TwoGonNoncrossingPocketInput`.
  The labels come from `exists_twoGonLabels`, the Euler equality from `reclosed_euler`, and the
  contradiction from `emptyTwoGonInput_holds`.

## Manuscript status

Infrastructure for `thm:hull` (through Osin's Lemma 9.7(a)); certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The noncrossing pocket of a two-gon of `Φ'_M`**, the geometric content of C6′.  Take the
binders of `TwoGonHoldsInput` and the labels of the two-gon given by `exists_twoGonLabels`: exterior
regions `a ≠ b` of the cell `i`, both targeting the section `j`, with the target arc of `a` ending
before that of `b` starts.  Then there are a source arc on the cell `i` and a target arc on the
oriented outer boundary such that the walk `source.reverseDarts ++ a.rightSide ++ target.darts ++
b.leftSide` is noncrossing, its outer cycle follows its boundary, the faces of `a` and `b` lie on
its side, no relator cell and no other selected region lies on its side, the source arc is at
least as long as the source arcs of `a` and `b` together, and the target arc runs from the start of
the target arc of `a` to the end of that of `b`. -/
def TwoGonNoncrossingPocketInput (D : RelGenSet G Lambda) (lambda c : ℝ) (eps : ℕ)
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
                              (hw.outerCycle S.diagram.planar).FollowsBoundary ∧
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

/-- **The exterior face is off the side of a noncrossing walk through the outer boundary.**  A
dart of a nonempty arc of the oriented outer boundary lies on the walk, and its reversal lies on
the exterior face, so the face across it is off the side of the walk. -/
theorem outerFace_not_mem_sideFaces_of_target_mem {W : Set (List (RelLetter G Lambda))}
    {X : DiscDiagram.{u, w, v} W} {walk : List X.toCombMap.Dart}
    (hw : IsNoncrossingClosedWalk X.toCombMap walk)
    (target : CyclicArc (targetDarts X none)) (hpos : 0 < target.length)
    (hsub : ∀ d ∈ target.darts, d ∈ walk) :
    X.outerFace ∉ SimpleClosedWalkSides.sideFaces X.toCombMap walk := by
  obtain ⟨d, hd⟩ := target.exists_mem_darts hpos
  have hcycle : d ∈ outerDarts X := target.mem_cycle_of_mem_darts hd
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hcycle
  have hface : X.toCombMap.faceOf e = X.outerFace :=
    ((X.faceBoundary X.outerFace).mem_iff e).mp (List.mem_reverse.mp he)
  have h := And.right ((hw.isBoundaryDart_sideFaces_iff X.planar _).mpr (hsub _ hd))
  rwa [X.toCombMap.alpha_involutive e, hface] at h

/-- **C6′ from the noncrossing pocket.**  The labels of the two-gon give exterior regions `a ≠ b`
of one cell to one section, the target arc of `a` first.  The noncrossing pocket walk of
`TwoGonNoncrossingPocketInput` has the exterior face off its side, from a dart of its target arc,
and the Euler equality of its side from `reclosed_euler`, so it is the inverse complement cycle of
the pocket region `PocketRegion.ofNoncrossingClosedWalk`.  That region holds `a` and `b`, no
relator cell and no other selected region, and its inverse complement cycle has the decomposition
of `EmptyTwoGonInput`, which `emptyTwoGonInput_holds` refutes. -/
theorem twoGonHoldsInput_of_noncrossingPocket {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
    {W : Set (List (RelLetter G Lambda))}
    (hpocket : TwoGonNoncrossingPocketInput.{u, w, v} D lambda c eps W) :
    TwoGonHoldsInput.{u, w, v} D lambda c eps W := by
  intro Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell
  obtain ⟨y, -, -, -, -, j, hya, hyb, hab, hja, hjb, horder⟩ :=
    RegionCandidate.exists_twoGonLabels S hmulti P hf hcorner
  obtain ⟨source, target, walk, hw, hwalk, hfollows, hsubA, hsubB, hcells, hothers, hsource,
      hstart, hend, htarget⟩ :=
    hpocket Delta cuts hlea S hloops hmulti a₀ ha₀ hat P f hf hcorner hcell _ j _ hya _ hyb hab
      hja hjb horder
  subst hwalk
  obtain ⟨-, hnd⟩ := S.nondegenerate _ (Finset.mem_filter.mp (Finset.mem_filter.mp hya).1).1
  have hpos : 0 < target.length := by omega
  have hout := outerFace_not_mem_sideFaces_of_target_mem hw target hpos
    (fun _ hd => List.mem_append_left _ (List.mem_append_right _ hd))
  have heuler := hw.reclosed_euler S.diagram.planar hfollows
  exact emptyTwoGonInput_holds D lambda c eps W Delta cuts hlea S _ j _ hya _ hyb hab hja hjb
    (PocketRegion.ofNoncrossingClosedWalk hw hout hfollows heuler) hsubA hsubB hcells hothers
    source target hsource hstart hend htarget
    (PocketRegion.ofNoncrossingClosedWalk_invDarts_outer hw hout hfollows heuler)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.TwoGonNoncrossingPocketInput
#audit_axioms GroupApproximation.GGT.VanKampen.outerFace_not_mem_sideFaces_of_target_mem
#audit_axioms GroupApproximation.GGT.VanKampen.twoGonHoldsInput_of_noncrossingPocket
