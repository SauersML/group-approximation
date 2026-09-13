import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueCarriers
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketPieces
import GroupApproximation.GGT.VanKampen.DiscEmbeddingAway
import GroupApproximation.Meta.AxiomGuard

/-!
# Transport of a pocket region to a cell

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a): a region of a copy of `Γ_1` to the arc
`t_1` of a cell `i` read backwards glues back into a region of a copy of `Δ` from a cell to `i`,
with the same contiguity degree.

Let `P` be a pocket region of `X` whose complement cycle follows the boundary, and `Ξ` an
O-equivalent copy of the pocket diagram, glued back along that cycle
(`PocketRegion.glueDiagram`).  The copy embeds into the glued diagram away from its outer face,
so a region of `Ξ` to `∂Ξ` keeps its face set, its source cell, its source arc and its sides.  When
its target arc lies on the part of `∂Ξ` glued to an arc of a cell `t` outside the pocket read
backwards, the image target darts read backwards a sub-arc of the image of `t`.

* `DiscEmbeddingAway.retargetGeometry`: a region transported along an embedding away from a face
  outside the region, with a given image source cell and a new target that carries the image of
  the target part of the boundary.
* `PocketRegion.glueCellArc`: the sub-arc of the image of the cell `t`.
* `PocketRegion.glueCellArc_boundaryDarts`: the sub-arc read backwards is the image target arc.
* `pocketCellTransport`: `PocketCellTransportStatement`.

## Manuscript status

Closes the binder `hcell` of the multiple-edge pocket cut transports
(`PocketRegion.fourSectionCuts_cellTransport`).  Infrastructure for `thm:hull` (tex 1636, through
Osin's Lemma 9.7(a)); certifies no printed sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open Embedded HullSC

universe u w v

namespace DiscEmbeddingAway

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Xi Y : DiscDiagram.{u, w, v} W} {f : Xi.toCombMap.Face} (E : DiscEmbeddingAway Xi Y f)

/-- A region avoiding `f` whose source cell has an image in `Y`, with a new target that carries
the image of the target part of the boundary, is a region of `Y` on the image face set. -/
def retargetGeometry {D : RelGenSet G Lambda} {eps : ℕ} {s : Finset Xi.toCombMap.Face}
    (hs : f ∉ s) (H : ContiguityGeometry D eps Xi s) (src : Fin Y.rCellCount)
    (hsrc : cellDarts Y src = (cellDarts Xi H.source).map E.darts)
    (T : List Xi.toCombMap.Dart)
    (hdec : H.boundary.cycle = H.sourceArc.reverseDarts ++ H.rightSide ++ T ++ H.leftSide)
    (target : Option (Fin Y.rCellCount)) (arc : CyclicArc (targetDarts Y target))
    (harc : targetBoundaryDarts Y target arc = T.map E.darts) :
    ContiguityGeometry D eps Y (E.faceSet s) where
  boundary := E.boundary s hs H.boundary
  source := src
  target := target
  sourceArc := H.sourceArc.mapTo E.darts hsrc
  targetArc := arc
  rightSide := H.rightSide.map E.darts
  leftSide := H.leftSide.map E.darts
  boundary_decomposition := by
    change H.boundary.cycle.map E.darts =
      (H.sourceArc.mapTo E.darts hsrc).reverseDarts ++ H.rightSide.map E.darts ++
        targetBoundaryDarts Y target arc ++ H.leftSide.map E.darts
    have hrev : (H.sourceArc.mapTo E.darts hsrc).reverseDarts =
        H.sourceArc.reverseDarts.map E.darts := by
      change invDarts Y (H.sourceArc.mapTo E.darts hsrc).darts =
        (invDarts Xi H.sourceArc.darts).map E.darts
      rw [CyclicArc.mapTo_darts, E.invDarts_map]
    rw [hrev, harc]
    exact (congrArg (List.map E.darts) hdec).trans (by simp only [List.map_append])
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

/-- The sub-arc of length `l` of the image of a cell outside the pocket, ending `m` darts before
the end of `arc`. -/
def glueCellArc (O : OEquivalentDiscDiagram P.diagram Xi) (hwalk : P.outer.FollowsBoundary)
    (d0 : (P.glueDiagram O hwalk).toCombMap.Dart) (t : Fin Delta.rCellCount)
    (ht : (cell Delta t).face ∉ P.faces) (arc : CyclicArc (cellDarts Delta t)) (m l : ℕ)
    (h : m + l ≤ arc.length) :
    CyclicArc (cellDarts (P.glueDiagram O hwalk) (P.glueLeftCell O hwalk t ht)) :=
  (arc.sub (arc.length - m - l) l (by omega)).mapTo (P.glueLeftDart O hwalk d0)
    (P.glueLeftCell_darts O hwalk t ht d0)

/-- **The image target arc reads a sub-arc of the cell backwards.**  Let the reversed complement
cycle read `arc` backwards after `pre`.  An arc of `∂Ξ` at offset `m` inside that part is carried
to the sub-arc of the image of the cell, read backwards. -/
theorem glueCellArc_boundaryDarts (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (d0 : (P.glueDiagram O hwalk).toCombMap.Dart)
    (t : Fin Delta.rCellCount) (ht : (cell Delta t).face ∉ P.faces)
    (arc : CyclicArc (cellDarts Delta t)) {pre post : List Delta.toCombMap.Dart}
    (hsplit : invDarts Delta P.outer.cycle = pre ++ invDarts Delta arc.darts ++ post)
    {c : List Xi.toCombMap.Dart} (tarc : CyclicArc c) (hc : c = outerDarts Xi) (m : ℕ)
    (hm : tarc.start.1 = pre.length + m) (h : m + tarc.length ≤ arc.length) :
    targetBoundaryDarts (P.glueDiagram O hwalk) (some (P.glueLeftCell O hwalk t ht))
        (P.glueCellArc O hwalk d0 t ht arc m tarc.length h) =
      tarc.darts.map (P.glueEmbeddingAway O hwalk).darts := by
  have hcl : P.outer.cycle.length = pre.length + arc.length + post.length := by
    have hlen := congrArg List.length hsplit
    simp only [invDarts_length, List.length_append, CyclicArc.darts_length] at hlen
    omega
  have hol : (outerDarts Xi).length = P.outer.cycle.length := by
    simp only [outerDarts, List.length_map, List.length_reverse]
    exact (P.glueSeam O).length_eq.symm
  have hwin := CyclicArc.darts_eq_drop_take tarc hc (by omega)
  have hcore := invDarts_window (P.glueDiagram O hwalk)
    ((invDarts Delta post).map (P.glueLeftDart O hwalk d0))
    (arc.darts.map (P.glueLeftDart O hwalk d0))
    ((invDarts Delta pre).map (P.glueLeftDart O hwalk d0)) m tarc.length
    (by rw [List.length_map, CyclicArc.darts_length]; exact h)
  simp only [List.length_map, invDarts_length, CyclicArc.darts_length] at hcore
  have hR : tarc.darts.map (P.glueEmbeddingAway O hwalk).darts =
      ((invDarts (P.glueDiagram O hwalk)
        ((invDarts Delta post).map (P.glueLeftDart O hwalk d0) ++
          arc.darts.map (P.glueLeftDart O hwalk d0) ++
          (invDarts Delta pre).map (P.glueLeftDart O hwalk d0))).drop
        (pre.length + m)).take tarc.length := by
    rw [hwin, List.map_take, List.map_drop, hm,
      show outerDarts Xi = invDarts Xi (Xi.faceBoundary Xi.outerFace).darts from rfl,
      ← (P.glueEmbeddingAway O hwalk).invDarts_map, P.glueOuter_darts O hwalk d0,
      cycle_eq_of_invDarts hsplit, List.map_append, List.map_append]
  change invDarts (P.glueDiagram O hwalk)
    (P.glueCellArc O hwalk d0 t ht arc m tarc.length h).darts = _
  unfold glueCellArc
  rw [CyclicArc.mapTo_darts, CyclicArc.sub_darts, List.map_take, List.map_drop, hR, hcore]

/-- A relator cell of the copy and a relator cell of `Δ` outside the pocket are different cells
of the glued diagram. -/
theorem glueRightCell_ne_glueLeftCell (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (i : Fin Xi.rCellCount) (t : Fin Delta.rCellCount)
    (ht : (cell Delta t).face ∉ P.faces) :
    P.glueRightCell O hwalk i ≠ P.glueLeftCell O hwalk t ht := by
  intro heq
  have hface := P.glueRightCell_face O hwalk i
  rw [heq, P.glueLeftCell_face] at hface
  exact (P.glueSeam O).leftFace_ne_rightFace _ _ hface

/-- A relator cell of the copy keeps its word length in the glued diagram. -/
theorem glueRightCell_word_length (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (i : Fin Xi.rCellCount) :
    (cell (P.glueDiagram O hwalk) (P.glueRightCell O hwalk i)).word.length =
      (cell Xi i).word.length := by
  rw [← dartWord_cellDarts (P.glueDiagram O hwalk) (P.glueRightCell O hwalk i),
    ← dartWord_cellDarts Xi i, P.glueRightCell_darts, (P.glueEmbeddingAway O hwalk).dartWord_map]

end PocketRegion

/-- **Transport to a cell** (Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(a)). -/
theorem pocketCellTransport : PocketCellTransportStatement.{u, w, v} := by
  intro G _ Lambda D eps W X P hwalk t ht arc pre post hsplit Xi O a hnone hlo hhi
  have hs : Xi.outerFace ∉ a.1 := fun h => (a.2.boundary.all_gCells _ h).1 rfl
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ (X.faceBoundary (cell X t).face).nonempty
  have d0 : (P.glueDiagram O hwalk).toCombMap.Dart :=
    (P.glueSeam O).faceDart d ((P.glueSeam O).faceOf_mem_of_mem_darts (cell X t).face
      ((P.mem_outside_iff _).2 ht) (X.faceBoundary (cell X t).face) d hd)
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hlo
  have hml : m + a.2.targetArc.length ≤ arc.length := by omega
  have hdec : a.2.boundary.cycle =
      a.2.sourceArc.reverseDarts ++ a.2.rightSide ++ a.2.targetArc.darts ++ a.2.leftSide :=
    a.2.boundary_decomposition.trans (by rw [targetBoundaryDarts_of_eq_none hnone a.2.targetArc])
  refine ⟨P.glueDiagram O hwalk,
    ⟨_, (P.glueEmbeddingAway O hwalk).retargetGeometry hs a.2
      (P.glueRightCell O hwalk a.2.source) (P.glueRightCell_darts O hwalk a.2.source)
      a.2.targetArc.darts hdec (some (P.glueLeftCell O hwalk t ht))
      (P.glueCellArc O hwalk d0 t ht arc m a.2.targetArc.length hml)
      (P.glueCellArc_boundaryDarts O hwalk d0 t ht arc hsplit a.2.targetArc
        (targetDarts_of_eq_none hnone) m hm hml)⟩,
    P.glueLeftCell O hwalk t ht, ⟨P.glueOEquivalent O hwalk⟩, rfl,
    P.glueRightCell_ne_glueLeftCell O hwalk a.2.source t ht, ?_⟩
  show ((a.2.sourceArc.mapTo (P.glueEmbeddingAway O hwalk).darts
      (P.glueRightCell_darts O hwalk a.2.source)).length : ℝ) /
      ((cell (P.glueDiagram O hwalk) (P.glueRightCell O hwalk a.2.source)).word.length : ℝ) =
    (a.2.sourceArc.length : ℝ) / ((cell Xi a.2.source).word.length : ℝ)
  rw [CyclicArc.mapTo_length, P.glueRightCell_word_length]

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.retargetGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueCellArc_boundaryDarts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueRightCell_ne_glueLeftCell
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueRightCell_word_length
#audit_closed_axioms GroupApproximation.GGT.VanKampen.pocketCellTransport
