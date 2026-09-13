import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketColourNoncrossing
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket face set of two exterior regions under the edge conditions

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

This module assembles the parity route to `SectionPocketFaceSetInput` on one diagram.  Two
distinct exterior regions of the cell `Π` to one section give the pocket walk `s_1 t_1 s_2 t_2` of
`PocketWalk.exists_of_exteriorAt`.

* The walk is a nonempty closed walk (`PocketWalk.exists_of_exteriorAt_closedWalk`).
* Every two-colouring of the faces changing colour exactly across the walk gives the faces of all
  walk darts one colour (`PocketWalkColour.walk_orient`).
* At least area, under the edge conditions `PocketWalk.CopyClean`, the walk has distinct darts and
  uses no edge in both directions (`PocketWalk.walk_nodup_and_alpha_not_mem`).
* With a relator cell on the side of the walk, the walk is the boundary cycle of a pocket face set
  in walk order (`PocketWalk.exists_pocketFaceSet_closedWalk_of_orient`).

* `PocketWalk.exists_pocketFaceSet_of_exteriorAt`: the assembled statement.

Not proved here: an O-equivalent copy with legal labels that satisfies the edge conditions, and
the relator cell on the side of the walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The pocket face set of two exterior regions.**  Let `a`, `b` be distinct exterior regions of
the cell `i` to the section `j`, and let `K` be the pocket walk of `exists_of_exteriorAt`, with
first side the left side of `y` and second side the right side of `x`, where `{x, y} = {a, b}`.
If the diagram has least area, `K` satisfies the edge conditions for `x` and `y`, and a relator
cell lies on the side of `K`, then `K` is the boundary cycle of a pocket face set in walk order. -/
theorem exists_pocketFaceSet_of_exteriorAt (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {a b : RegionCandidate D eps S.diagram}
    (ha : a ∈ RegionCandidate.exteriorAt S.family i)
    (hb : b ∈ RegionCandidate.exteriorAt S.family i) (hab : a ≠ b)
    (hja : RegionCandidate.TargetsSectionIndex cuts j a)
    (hjb : RegionCandidate.TargetsSectionIndex cuts j b) :
    ∃ (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
      (x y : RegionCandidate D eps S.diagram), (x = a ∧ y = b ∨ x = b ∧ y = a) ∧
      K.source = i ∧ K.firstSide = y.2.leftSide ∧ K.secondSide = x.2.rightSide ∧
        (∃ Gap : CyclicArc (cellDarts S.diagram i),
          K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts) ∧
        K.targetArc.start.1 = x.2.targetArc.start.1 ∧
        K.targetArc.start.1 + K.targetArc.length =
          y.2.targetArc.start.1 + y.2.targetArc.length ∧
        (S.diagram.LeastArea → K.CopyClean x y →
          (∃ kept : Fin S.diagram.rCellCount,
            (cell S.diagram kept).face ∈ sideFaces S.diagram.toCombMap K.walk) →
          ∃ P : PocketFaceSet D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ),
            P.boundary.cycle = K.walk ∧ P.ClosedWalk) := by
  obtain ⟨K, x, y, hxy, hKi, hfirst, hsecond, hgap, hstart, hend, hne, hchain, hcloses⟩ :=
    exists_of_exteriorAt_closedWalk S ha hb hab hja hjb
  have hmem : x ∈ RegionCandidate.exteriorAt S.family i ∧
      y ∈ RegionCandidate.exteriorAt S.family i ∧ x ≠ y := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨ha, hb, hab⟩
    · exact ⟨hb, ha, hab.symm⟩
  refine ⟨K, x, y, hxy, hKi, hfirst, hsecond, hgap, hstart, hend, fun hlea hclean hkept => ?_⟩
  have hdisj : Disjoint x.1 y.1 :=
    S.pairwise x (PocketWalkColour.mem_exteriorAt S hmem.1).1 y
      (PocketWalkColour.mem_exteriorAt S hmem.2.1).1 hmem.2.2
  obtain ⟨hnodup, halpha⟩ := K.walk_nodup_and_alpha_not_mem hlea hfirst hsecond hdisj hclean
  exact K.exists_pocketFaceSet_closedWalk_of_orient hne hnodup halpha hchain hcloses
    (fun _ hcol => PocketWalkColour.walk_orient S hmem.1 hmem.2.1 hmem.2.2 K hKi hfirst hsecond
      hgap hstart hcol) hkept

end PocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.exists_pocketFaceSet_of_exteriorAt
