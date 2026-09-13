import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueEquivalence
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcSub
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap
import GroupApproximation.GGT.VanKampen.FaceShelling
import GroupApproximation.GGT.VanKampen.FaceSetBoundaryWalk
import GroupApproximation.Meta.AxiomGuard

/-!
# Carriers of the glued diagram

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): regions of copies of `Γ_1` glue back
into regions of copies of `Δ`.

Let `P` be a pocket region of `Δ` and `Ξ` an O-equivalent copy of the pocket diagram, glued back
along the complement cycle (`PocketRegion.glueDiagram`).  This file computes the carriers that a
region of `Ξ` reads in the glued diagram.

* `PocketRegion.glueRightCell_darts`: a relator cell of `Ξ` keeps its carrier, through the
  embedding of `Ξ`.
* `PocketRegion.glueLeftCell_darts`: a relator cell of `Δ` outside the pocket keeps its carrier.
* `PocketRegion.glueOuter_darts`: the outer face of `Ξ` is glued to the complement cycle.
* `Embedded.invDarts_window`: a window in the middle part of a reversed concatenation.

## Manuscript status

Infrastructure for Osin's Lemma 9.7 through the pocket glue modules; certifies no printed
sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v

namespace Embedded

/-- A window of a reversed list is the reverse of the mirrored window. -/
theorem reverse_drop_take {α : Type*} (L : List α) (m l : ℕ) (h : m + l ≤ L.length) :
    (L.reverse.drop m).take l = ((L.drop (L.length - m - l)).take l).reverse := by
  have hlen : (L.take (L.length - m)).length = L.length - m := by
    rw [List.length_take]
    omega
  rw [List.drop_reverse, List.take_reverse, hlen, List.drop_take,
    show L.length - m - (L.length - m - l) = l by omega]

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A window inside the middle part of a reversed concatenation. -/
theorem invDarts_window (Delta : DiscDiagram.{u, w, v} W) (B3 M B1 : List Delta.toCombMap.Dart)
    (m l : ℕ) (h : m + l ≤ M.length) :
    ((invDarts Delta (B3 ++ M ++ B1)).drop (B1.length + m)).take l =
      invDarts Delta ((M.drop (M.length - m - l)).take l) := by
  have h1 : m ≤ (invDarts Delta M).length := by
    rw [invDarts_length]
    omega
  have h2 : l ≤ ((invDarts Delta M).drop m).length := by
    rw [List.length_drop, invDarts_length]
    omega
  rw [invDarts_append, invDarts_append, ← invDarts_length B1, List.drop_length_add_append,
    List.drop_append_of_le_length h1, List.take_append_of_le_length h2]
  change ((M.reverse.map Delta.toCombMap.alpha).drop m).take l =
    ((M.drop (M.length - m - l)).take l).reverse.map Delta.toCombMap.alpha
  rw [← List.map_drop, ← List.map_take, reverse_drop_take M m l h]

/-- A cycle read off a split of its reversal. -/
theorem cycle_eq_of_invDarts {Delta : DiscDiagram.{u, w, v} W}
    {c pre mid post : List Delta.toCombMap.Dart}
    (h : invDarts Delta c = pre ++ invDarts Delta mid ++ post) :
    c = invDarts Delta post ++ mid ++ invDarts Delta pre := by
  have h2 := congrArg (invDarts Delta) h
  rw [invDarts_invDarts, invDarts_append, invDarts_append, invDarts_invDarts] at h2
  rw [h2, List.append_assoc]

namespace CyclicArc

/-- An arc that does not wrap around reads a window of its carrier. -/
theorem darts_eq_drop_take {Dart : Type v} {c c' : List Dart} (arc : CyclicArc c)
    (hc : c = c') (h : arc.start.1 + arc.length ≤ c'.length) :
    arc.darts = (c'.drop arc.start.1).take arc.length := by
  subst c'
  have hl : arc.length ≤ (c.drop arc.start.1).length := by
    rw [List.length_drop]
    omega
  exact List.take_append_of_le_length hl

end CyclicArc

variable {Delta : DiscDiagram.{u, w, v} W}

theorem targetDarts_of_eq_none {target : Option (Fin Delta.rCellCount)} (h : target = none) :
    targetDarts Delta target = outerDarts Delta := by
  subst h
  rfl

theorem targetBoundaryDarts_of_eq_none {target : Option (Fin Delta.rCellCount)}
    (h : target = none) (arc : CyclicArc (targetDarts Delta target)) :
    targetBoundaryDarts Delta target arc = arc.darts := by
  subst h
  rfl

end Embedded

namespace Surgery.PocketGlue.Seam

variable {M X : CombMap.{v}} (S : Seam M X)

open scoped Classical in
/-- A dart of `M` as a glued dart: the dart itself on `faces`, and `d0` elsewhere. -/
def leftIncl (d0 : S.glueMap.Dart) (d : M.Dart) : S.glueMap.Dart :=
  if hd : M.faceOf d ∈ S.faces then S.faceDart d hd else d0

theorem leftIncl_of_mem (d0 : S.glueMap.Dart) {d : M.Dart} (hd : M.faceOf d ∈ S.faces) :
    S.leftIncl d0 d = S.faceDart d hd := by
  unfold leftIncl
  exact dif_pos hd

theorem leftDarts_eq_map (d0 : S.glueMap.Dart) (g : M.Face) (hg : g ∈ S.faces)
    (B : FaceBoundary M g) : S.leftDarts g hg B = B.darts.map (S.leftIncl d0) := by
  unfold leftDarts
  rw [← List.pmap_eq_map (p := fun d => M.faceOf d ∈ S.faces) (S.faceOf_mem_of_mem_darts g hg B)]
  exact List.pmap_congr_left B.darts fun _ _ h₁ _ => (S.leftIncl_of_mem d0 h₁).symm

/-- The traversal of `outer` is glued to the boundary cycle of `faces`. -/
theorem outerBoundary_map_glueEmbedding (d0 : S.glueMap.Dart) :
    S.outerBoundary.darts.map S.glueEmbedding = S.boundary.cycle.map (S.leftIncl d0) := by
  refine List.ext_getElem (by rw [List.length_map, List.length_map, S.length_eq]) ?_
  intro i h₁ h₂
  have hi : i < S.boundary.cycle.length := by
    rw [List.length_map] at h₂
    exact h₂
  have hd : M.faceOf S.boundary.cycle[i] ∈ S.faces :=
    ((S.boundary.cycle_mem_iff _).1 (List.getElem_mem hi)).1
  have hseam : (S.seamEquiv (S.boundary.positionEquiv ⟨i, hi⟩)).1 =
      S.outerBoundary.darts[i]'(by rw [← S.length_eq]; exact hi) := by
    rw [S.seamEquiv_positionEquiv]
    exact S.outerPosition_val _
  rw [List.getElem_map, List.getElem_map, ← hseam, S.leftIncl_of_mem d0 hd]
  exact S.glueEmbedding_seam _

end Surgery.PocketGlue.Seam

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta) {Xi : DiscDiagram.{u, w, v} W}

/-- The relator cell of the glued diagram carrying a relator cell of the copy. -/
def glueRightCell (O : OEquivalentDiscDiagram P.diagram Xi) (hwalk : P.outer.FollowsBoundary)
    (i : Fin Xi.rCellCount) : Fin (P.glueDiagram O hwalk).rCellCount :=
  (cellFaceEquiv (P.glueDiagram O hwalk)).symm
    ⟨(P.glueSeam O).rightFace ⟨(Embedded.cell Xi i).face, (Embedded.cell Xi i).face_ne_outer⟩,
      P.glueRight_mem O hwalk (List.mem_map_of_mem (Embedded.cell_mem Xi i))⟩

theorem glueRightCell_face (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (i : Fin Xi.rCellCount) :
    (Embedded.cell (P.glueDiagram O hwalk) (P.glueRightCell O hwalk i)).face =
      (P.glueSeam O).rightFace ⟨(Embedded.cell Xi i).face, (Embedded.cell Xi i).face_ne_outer⟩ := by
  have h := congrArg Subtype.val ((cellFaceEquiv (P.glueDiagram O hwalk)).apply_symm_apply
    ⟨(P.glueSeam O).rightFace ⟨(Embedded.cell Xi i).face, (Embedded.cell Xi i).face_ne_outer⟩,
      P.glueRight_mem O hwalk (List.mem_map_of_mem (Embedded.cell_mem Xi i))⟩)
  rw [cellFaceEquiv_val] at h
  exact h

/-- A relator cell of the copy keeps its carrier in the glued diagram. -/
theorem glueRightCell_darts (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (i : Fin Xi.rCellCount) :
    Embedded.cellDarts (P.glueDiagram O hwalk) (P.glueRightCell O hwalk i) =
      (Embedded.cellDarts Xi i).map (P.glueEmbeddingAway O hwalk).darts :=
  (congrArg (fun F => ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary F).darts)
    (P.glueRightCell_face O hwalk i)).trans
    ((P.glueSeam O).glueFaceBoundary_rightFace_darts Delta.faceBoundary Xi.faceBoundary
      (Embedded.cell Xi i).face (Embedded.cell Xi i).face_ne_outer)

/-- The relator cell of the glued diagram carrying a relator cell of `Δ` outside the pocket. -/
def glueLeftCell (O : OEquivalentDiscDiagram P.diagram Xi) (hwalk : P.outer.FollowsBoundary)
    (t : Fin Delta.rCellCount) (ht : (Embedded.cell Delta t).face ∉ P.faces) :
    Fin (P.glueDiagram O hwalk).rCellCount :=
  (cellFaceEquiv (P.glueDiagram O hwalk)).symm
    ⟨(P.glueSeam O).leftFace ⟨(Embedded.cell Delta t).face, (P.mem_outside_iff _).2 ht⟩,
      P.glueLeft_mem O hwalk (List.mem_map_of_mem (Embedded.cell_mem Delta t))
        ((P.mem_outside_iff _).2 ht)⟩

theorem glueLeftCell_face (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (t : Fin Delta.rCellCount)
    (ht : (Embedded.cell Delta t).face ∉ P.faces) :
    (Embedded.cell (P.glueDiagram O hwalk) (P.glueLeftCell O hwalk t ht)).face =
      (P.glueSeam O).leftFace ⟨(Embedded.cell Delta t).face, (P.mem_outside_iff _).2 ht⟩ := by
  have h := congrArg Subtype.val ((cellFaceEquiv (P.glueDiagram O hwalk)).apply_symm_apply
    ⟨(P.glueSeam O).leftFace ⟨(Embedded.cell Delta t).face, (P.mem_outside_iff _).2 ht⟩,
      P.glueLeft_mem O hwalk (List.mem_map_of_mem (Embedded.cell_mem Delta t))
        ((P.mem_outside_iff _).2 ht)⟩)
  rw [cellFaceEquiv_val] at h
  exact h

/-- A dart of `Δ` as a dart of the glued diagram: itself on the complement, `d0` elsewhere. -/
def glueLeftDart (O : OEquivalentDiscDiagram P.diagram Xi) (hwalk : P.outer.FollowsBoundary)
    (d0 : (P.glueDiagram O hwalk).toCombMap.Dart) (d : Delta.toCombMap.Dart) :
    (P.glueDiagram O hwalk).toCombMap.Dart :=
  (P.glueSeam O).leftIncl d0 d

/-- A relator cell of `Δ` outside the pocket keeps its carrier in the glued diagram. -/
theorem glueLeftCell_darts (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (t : Fin Delta.rCellCount)
    (ht : (Embedded.cell Delta t).face ∉ P.faces) (d0 : (P.glueDiagram O hwalk).toCombMap.Dart) :
    Embedded.cellDarts (P.glueDiagram O hwalk) (P.glueLeftCell O hwalk t ht) =
      (Embedded.cellDarts Delta t).map (P.glueLeftDart O hwalk d0) :=
  (congrArg (fun F => ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary F).darts)
    (P.glueLeftCell_face O hwalk t ht)).trans
    (((P.glueSeam O).glueFaceBoundary_leftFace_darts Delta.faceBoundary Xi.faceBoundary
      (Embedded.cell Delta t).face ((P.mem_outside_iff _).2 ht)).trans
      ((P.glueSeam O).leftDarts_eq_map d0 _ _ _))

/-- The outer face of the copy is glued to the complement cycle. -/
theorem glueOuter_darts (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (d0 : (P.glueDiagram O hwalk).toCombMap.Dart) :
    (Xi.faceBoundary Xi.outerFace).darts.map (P.glueEmbeddingAway O hwalk).darts =
      P.outer.cycle.map (P.glueLeftDart O hwalk d0) :=
  (P.glueSeam O).outerBoundary_map_glueEmbedding d0

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.reverse_drop_take
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.invDarts_window
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.cycle_eq_of_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CyclicArc.darts_eq_drop_take
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.targetDarts_of_eq_none
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.targetBoundaryDarts_of_eq_none
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.leftDarts_eq_map
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.outerBoundary_map_glueEmbedding
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueRightCell_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueLeftCell_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueOuter_darts
