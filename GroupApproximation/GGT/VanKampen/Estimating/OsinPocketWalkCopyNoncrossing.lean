import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkChain
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketWalkColour
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCopyWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketColourNoncrossing
import GroupApproximation.Meta.AxiomGuard

/-!
# The pocket walk of two exterior regions is noncrossing under the edge conditions

Osin, arXiv:math/0411039v3, proof of Lemma 9.7(b):

> "Let us consider the subdiagram `Γ_1` of `Δ` such that: (i) `∂Γ_1 = s_1 t_1 s_2 t_2`, where
> `s_1, s_2` are side arcs of some of `Γ_{i,1}`'s and `t_1, t_2` are subpaths of `∂Π` and the
> section `q_1` of `∂Δ`, respectively; (ii) `Γ_1` contains all `Γ_{i,1}`'s."

This module proves the input `hnc` of `GloballyDistinguishedSectionFamily.false_of_unpinched`
(`Estimating/OsinPocketKeptCellUnpinched.lean`) and of `exists_kept_of_noncrossing_of_value`
(`Estimating/OsinPocketKeptCellNoncrossing.lean`) for a pocket walk `K` given with the data of
`PocketWalk.exists_of_exteriorAt`.  It combines four landed steps of the parity route.

* `PocketWalk.walk_isChain_closes`: `K.walk` is a closed walk.
* `PocketWalk.walk_nodup_and_alpha_not_mem`: at least area, under the edge conditions
  `PocketWalk.CopyClean`, the walk has distinct darts and uses no edge in both directions.
* `PocketWalkColour.walk_orient`: every two-colouring of the faces changing colour exactly across
  the walk gives the faces of all walk darts one colour.
* `ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient`: so the walk is noncrossing.

* `PocketWalk.isNoncrossingClosedWalk_of_copyClean`: the assembled statement.

The clause `cell_outer` of the edge conditions is needed.  A dart of `Π` that lies in the source
arc of `K` and has the exterior face across it can also lie in the target arc of `K`, and then the
walk holds that dart and its reverse.

Not proved here: an O-equivalent copy of the diagram satisfying the edge conditions.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7;
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace PocketWalk

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The pocket walk of two exterior regions is noncrossing under the edge conditions.**  Let
`x ≠ y` be exterior regions of the cell `i`, with `y` targeting the section `j`.  Let `K` be a
pocket walk from the cell `i` to the section `j`, with first side the left side of `y` and second
side the right side of `x`.  Let its source arc span the source arcs of `x` and `y` with a gap
between, and let its target arc start where that of `x` starts and end where that of `y` ends.  If
the diagram has least area and `K` satisfies the edge conditions for `x` and `y`, then `K.walk` is
a noncrossing closed walk. -/
theorem isNoncrossingClosedWalk_of_copyClean
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {i : Fin S.diagram.rCellCount} {j : Fin cuts.count} {x y : RegionCandidate D eps S.diagram}
    (hx : x ∈ RegionCandidate.exteriorAt S.family i)
    (hy : y ∈ RegionCandidate.exteriorAt S.family i) (hxy : x ≠ y)
    (hjy : RegionCandidate.TargetsSectionIndex cuts j y)
    (K : PocketWalk D eps S.diagram (cuts.cut j.castSucc) (cuts.cut j.succ))
    (hsource : K.source = i)
    (hfirst : K.firstSide = y.2.leftSide) (hsecond : K.secondSide = x.2.rightSide)
    (hgap : ∃ Gap : CyclicArc (cellDarts S.diagram i),
      K.sourceArc.darts = x.2.sourceArc.darts ++ Gap.darts ++ y.2.sourceArc.darts)
    (hstart : K.targetArc.start.1 = x.2.targetArc.start.1)
    (hend : K.targetArc.start.1 + K.targetArc.length =
      y.2.targetArc.start.1 + y.2.targetArc.length)
    (hlea : S.diagram.LeastArea) (hclean : K.CopyClean x y) :
    IsNoncrossingClosedWalk S.diagram.toCombMap K.walk := by
  obtain ⟨hxS, -, hxt⟩ := PocketWalkColour.mem_exteriorAt S hx
  obtain ⟨hyS, -, hyt⟩ := PocketWalkColour.mem_exteriorAt S hy
  obtain ⟨hxs, hxtgt⟩ := S.nondegenerate x hxS
  obtain ⟨hys, hytgt⟩ := S.nondegenerate y hyS
  obtain ⟨-, -, hyhi⟩ := hjy
  have hyend : y.2.targetArc.start.1 + y.2.targetArc.length ≤ (outerDarts S.diagram).length :=
    Nat.le_trans hyhi (cut_le_length_outerDarts S j.succ)
  obtain ⟨Gap, hsrc⟩ := hgap
  obtain ⟨hchain, hcloses⟩ := K.walk_isChain_closes x y hxt hyt hxs hys hxtgt hytgt hfirst
    hsecond Gap.darts hsrc hstart hend hyend
  obtain ⟨hnodup, halpha⟩ := K.walk_nodup_and_alpha_not_mem hlea hfirst hsecond
    (S.pairwise x hxS y hyS hxy) hclean
  exact ClosedWalkFaceColouring.isNoncrossingClosedWalk_of_orient S.diagram.planar
    K.walk_ne_nil hnodup halpha hchain
    (hcloses _ (Option.mem_def.mpr (List.getLast?_eq_some_getLast K.walk_ne_nil)) _
      (Option.mem_def.mpr (List.head?_eq_some_head K.walk_ne_nil)))
    fun _ hcol => PocketWalkColour.walk_orient S hx hy hxy K hsource hfirst hsecond
      ⟨Gap, hsrc⟩ hstart hcol

end PocketWalk

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.PocketWalk.isNoncrossingClosedWalk_of_copyClean
