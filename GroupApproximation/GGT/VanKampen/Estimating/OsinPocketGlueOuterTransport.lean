import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueEquivalence
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueOuterArc
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.GGT.VanKampen.Estimating.Partition
import GroupApproximation.GGT.VanKampen.DiscEmbeddingAway
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport of a pocket region to the boundary

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): a region of a copy of `Γ_1` to the arc
`t_2` of the section `q_j` glues back into a region of a copy of `Δ` to `q_j`, with the same
contiguity degree.

Let `P` be a pocket region of `X` whose complement cycle follows the boundary, and `Ξ` an
O-equivalent copy of the pocket diagram, glued back along that cycle
(`PocketRegion.glueDiagram`).  The copy embeds into the glued diagram away from its outer face,
so a region of `Ξ` to `∂Ξ` keeps its face set, its source cell, its source arc and its sides.  When
its target arc lies on the part of `∂Ξ` glued to an arc of `∂X`, the image target arc lies on
`∂` of the glued diagram inside that arc (`PocketRegion.exists_glue_outerArc_within`).

* `DiscEmbeddingAway.outerGeometry`: a region to the boundary, transported along an embedding
  away from a face outside the region, with a given image source cell and target arc.
* `PocketRegion.exists_glue_cell`: a relator cell of the copy is a relator cell of the glued
  diagram with the image carrier.
* `PocketRegion.exists_glue_outerCandidate`: the transported region of the glued diagram.
* `pocketOuterTransport`: `PocketOuterTransportStatement`.

## Manuscript status

Closes the binder `houter` of the section pocket cut assembly (`OsinPocketPieces`).
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open Embedded HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v v'

namespace DiscEmbeddingAway

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {f : Delta.toCombMap.Face} (E : DiscEmbeddingAway Delta Xi f)

/-- A region avoiding `f` whose source cell and target arc have images in `Xi` is a region of
`Xi` to `∂Xi` on the image face set. -/
def outerGeometry {D : RelGenSet G Lambda} {eps : ℕ} {s : Finset Delta.toCombMap.Face}
    (hs : f ∉ s) (H : ContiguityGeometry D eps Delta s) (j : Fin Xi.rCellCount)
    (hj : cellDarts Xi j = (cellDarts Delta H.source).map E.darts)
    (B : CyclicArc (outerDarts Xi))
    (hB : B.darts = (targetBoundaryDarts Delta H.target H.targetArc).map E.darts) :
    ContiguityGeometry D eps Xi (E.faceSet s) where
  boundary := E.boundary s hs H.boundary
  source := j
  target := none
  sourceArc := H.sourceArc.mapTo E.darts hj
  targetArc := B
  rightSide := H.rightSide.map E.darts
  leftSide := H.leftSide.map E.darts
  boundary_decomposition := by
    change H.boundary.cycle.map E.darts =
      (H.sourceArc.mapTo E.darts hj).reverseDarts ++ H.rightSide.map E.darts ++ B.darts ++
        H.leftSide.map E.darts
    have hrev : (H.sourceArc.mapTo E.darts hj).reverseDarts =
        H.sourceArc.reverseDarts.map E.darts := by
      change invDarts Xi (H.sourceArc.mapTo E.darts hj).darts =
        (invDarts Delta H.sourceArc.darts).map E.darts
      rw [CyclicArc.mapTo_darts, E.invDarts_map]
    rw [hrev, hB]
    exact (congrArg (List.map E.darts) H.boundary_decomposition).trans
      (by simp only [List.map_append])
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by rw [E.dartWord_map]; exact H.rightSide_norm_le
  leftSide_norm_le := by rw [E.dartWord_map]; exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map E.faces, E.shelling s hs hl⟩

end DiscEmbeddingAway

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta) {Xi : DiscDiagram.{u, w, v} W}

/-- A relator cell of the copy is a relator cell of the glued diagram, with the image carrier. -/
theorem exists_glue_cell (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (i : Fin Xi.rCellCount) :
    ∃ j : Fin (P.glueDiagram O hwalk).rCellCount, cellDarts (P.glueDiagram O hwalk) j =
      (cellDarts Xi i).map (P.glueEmbeddingAway O hwalk).darts := by
  have hmem : (cell Xi i).face ∈ Xi.relatorCells.map RelatorCell.face :=
    List.mem_map_of_mem (cell_mem Xi i)
  have hne := DiscDiagram.relFace_ne_outerFace hmem
  obtain ⟨C, hC, hCF⟩ := List.mem_map.1 (P.glueRight_mem O hwalk hmem)
  obtain ⟨n, hn⟩ := List.get_of_mem hC
  refine ⟨n, ?_⟩
  have hface : (cell (P.glueDiagram O hwalk) n).face =
      (P.glueEmbeddingAway O hwalk).faces (cell Xi i).face :=
    (congrArg RelatorCell.face hn).trans (hCF.trans (P.glueXFace_of_ne O _ hne).symm)
  exact (congrArg (fun F => ((P.glueDiagram O hwalk).faceBoundary F).darts) hface).trans
    ((P.glueEmbeddingAway O hwalk).face_boundary _ hne)

/-- A region of the copy to the part of `∂Ξ` glued to an arc of `∂Δ` is a region of the glued
diagram to `∂` inside that arc, with the same contiguity degree. -/
theorem exists_glue_outerCandidate {D : RelGenSet G Lambda} {eps : ℕ}
    (O : OEquivalentDiscDiagram P.diagram Xi) (hwalk : P.outer.FollowsBoundary)
    (arc : CyclicArc (outerDarts Delta))
    (hend : arc.start.1 + arc.length ≤ (outerDarts Delta).length)
    (pre post : List Delta.toCombMap.Dart)
    (hdec : invDarts Delta P.outer.cycle = pre ++ arc.darts ++ post)
    (a : RegionCandidate D eps Xi) (ht : a.2.target = none)
    (hpre : pre.length ≤ a.2.targetArc.start.1)
    (hA : a.2.targetArc.start.1 + a.2.targetArc.length ≤ pre.length + arc.length) :
    ∃ b : RegionCandidate D eps (P.glueDiagram O hwalk), b.2.target = none ∧
      arc.start.1 ≤ b.2.targetArc.start.1 ∧
      b.2.targetArc.start.1 + b.2.targetArc.length ≤ arc.start.1 + arc.length ∧
      b.contiguityDegree = a.contiguityDegree := by
  obtain ⟨s, H⟩ := a
  obtain ⟨boundary, source, target, sourceArc, targetArc, rightSide, leftSide, hdecomp,
    hrl, hll, hrn, hln, hpaste⟩ := H
  change target = none at ht
  subst ht
  have hs : Xi.outerFace ∉ s := fun h => (boundary.all_gCells _ h).1 rfl
  obtain ⟨B, hb1, hb2, hBd⟩ :=
    P.exists_glue_outerArc_within O hwalk arc hend pre post hdec targetArc hpre hA
  obtain ⟨j, hj⟩ := P.exists_glue_cell O hwalk source
  refine ⟨⟨_, (P.glueEmbeddingAway O hwalk).outerGeometry hs
    ⟨boundary, source, none, sourceArc, targetArc, rightSide, leftSide, hdecomp, hrl, hll,
      hrn, hln, hpaste⟩ j hj B hBd⟩, rfl, hb1, hb2, ?_⟩
  have hw : (cell (P.glueDiagram O hwalk) j).word.length = (cell Xi source).word.length :=
    (CellBoundaryPartition.cellDarts_length_eq_word_length _ j).symm.trans
      (((congrArg List.length hj).trans (List.length_map _)).trans
        (CellBoundaryPartition.cellDarts_length_eq_word_length Xi source))
  change ((sourceArc.mapTo (P.glueEmbeddingAway O hwalk).darts hj).length : ℝ) /
      ((cell (P.glueDiagram O hwalk) j).word.length : ℝ) =
    (sourceArc.length : ℝ) / ((cell Xi source).word.length : ℝ)
  rw [sourceArc.mapTo_length, hw]

end PocketRegion

/-- **Transport to the boundary** (Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b)). -/
theorem pocketOuterTransport : PocketOuterTransportStatement.{u, w, v} := by
  intro G _ Lambda D eps W X P hwalk arc hend pre post hdec Xi O a ht hpre hA
  obtain ⟨b, hbt, hb1, hb2, hbd⟩ :=
    P.exists_glue_outerCandidate O hwalk arc hend pre post hdec a ht hpre hA
  exact ⟨P.glueDiagram O hwalk, b, ⟨P.glueOEquivalent O hwalk⟩, hbt, hb1, hb2, hbd⟩

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.outerGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_glue_cell
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_glue_outerCandidate
#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketOuterTransport
