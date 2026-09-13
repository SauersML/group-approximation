import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketRegion
import GroupApproximation.GGT.VanKampen.SurgeryPocketGlueFaces
import GroupApproximation.GGT.VanKampen.DiscEmbeddingAway
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.Meta.AxiomGuard

/-!
# Gluing a copy of the pocket back into the diagram

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): regions of copies of `Γ_1` glue back
into regions of copies of `Δ`.

Let `P` be a pocket region of `Δ` and `Ξ` an O-equivalent copy of the pocket diagram.  The outer
face of `Ξ` reads the boundary cycle of the complement of `P`, so `Ξ` glues into that cycle along
a `Seam`.  When the cycle follows the boundary of the complement, the glued map is planar, and it
is a disc diagram with the boundary word of `Δ`.  Its relator faces carry the relator cells of
`Δ` outside the pocket and the relator cells of `Ξ`, and `Ξ` embeds into it away from the outer
face of `Ξ`.

* `PocketRegion.outerWord_eq_of_oEquivalent`: the outer face of `Ξ` reads the complement cycle.
* `PocketRegion.glueSeam`: the seam of the complement and the outer face of `Ξ`.
* `PocketRegion.glueDiagram`: the glued disc diagram.
* `PocketRegion.glueDiagram_boundaryWord`: it has the boundary word of `Δ`.
* `PocketRegion.glueDiagram_face_mem_iff`: its relator faces.
* `PocketRegion.glueEmbeddingAway`: `Ξ` embeds into it away from the outer face of `Ξ`.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v

namespace Surgery.PocketGlue.Seam

variable {M X : CombMap.{v}} (S : Seam M X)

/-- Every glued face carries a face in `faces` or a face of `X` other than `outer`. -/
theorem exists_leftFace_or_rightFace (F : S.glueMap.Face) :
    (∃ g : M.Face, ∃ hg : g ∈ S.faces, F = S.leftFace ⟨g, hg⟩) ∨
      ∃ h : X.Face, ∃ hh : h ≠ S.outer, F = S.rightFace ⟨h, hh⟩ := by
  obtain ⟨s, rfl⟩ := S.glueFaceEquiv.symm.surjective F
  rcases s with ⟨g, hg⟩ | ⟨h, hh⟩
  · exact Or.inl ⟨g, hg, rfl⟩
  · exact Or.inr ⟨h, hh, rfl⟩

end Surgery.PocketGlue.Seam

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta) {Xi : DiscDiagram.{u, w, v} W}

/-- The outer face of an O-equivalent copy of the pocket reads the boundary cycle of the
complement. -/
theorem outerWord_eq_of_oEquivalent (O : OEquivalentDiscDiagram P.diagram Xi) :
    (Xi.faceBoundary Xi.outerFace).darts.map Xi.label = P.outer.cycle.map Delta.label := by
  have h : RelWord.revInv ((Xi.faceBoundary Xi.outerFace).darts.map Xi.label) =
      RelWord.revInv (P.outer.cycle.map Delta.label) :=
    (O.boundaryWord_eq.trans P.diagram_boundaryWord).trans
      (Embedded.dartWord_reverse_alpha Delta P.outer.cycle)
  have h2 := congrArg RelWord.revInv h
  rewrite [RelWord.revInv_revInv, RelWord.revInv_revInv] at h2
  exact h2

/-- The seam of the complement of the pocket and the outer face of an O-equivalent copy. -/
def glueSeam (O : OEquivalentDiscDiagram P.diagram Xi) : Seam Delta.toCombMap Xi.toCombMap where
  faces := P.outside
  boundary := P.outer.toBoundaryCycle
  outer := Xi.outerFace
  outerBoundary := Xi.faceBoundary Xi.outerFace
  length_eq := by
    have h := congrArg List.length (P.outerWord_eq_of_oEquivalent O)
    rewrite [List.length_map, List.length_map] at h
    exact h.symm

/-- The labels agree along the seam. -/
theorem glueSeam_label (O : OEquivalentDiscDiagram P.diagram Xi)
    (b : BoundaryDart Delta.toCombMap (P.glueSeam O).faces) :
    Xi.label ((P.glueSeam O).seamEquiv b).1 = Delta.label b.1 := by
  obtain ⟨i, rfl⟩ := (P.glueSeam O).boundary.positionEquiv.surjective b
  rewrite [Seam.seamEquiv_positionEquiv, Seam.outerPosition_val]
  have hget := (List.ext_getElem_iff.1 (P.outerWord_eq_of_oEquivalent O)).2 i.1
    (by
      rewrite [List.length_map]
      exact ((P.glueSeam O).positionCast i).2)
    (by
      rewrite [List.length_map]
      exact i.2)
  rewrite [List.getElem_map, List.getElem_map] at hget
  exact hget

open scoped Classical in
/-- The relator faces of the glued map: the faces of the relator cells of `Δ` outside the pocket
and of the relator cells of the copy. -/
def glueRelFaces (O : OEquivalentDiscDiagram P.diagram Xi) :
    Finset (P.glueSeam O).glueMap.Face :=
  Finset.univ.filter fun F =>
    (∃ C ∈ Delta.relatorCells, ∃ hC : C.face ∈ P.outside,
        (P.glueSeam O).leftFace ⟨C.face, hC⟩ = F) ∨
      ∃ C ∈ Xi.relatorCells, (P.glueSeam O).rightFace ⟨C.face, C.face_ne_outer⟩ = F

theorem mem_glueRelFaces (O : OEquivalentDiscDiagram P.diagram Xi)
    (F : (P.glueSeam O).glueMap.Face) :
    F ∈ P.glueRelFaces O ↔
      (∃ C ∈ Delta.relatorCells, ∃ hC : C.face ∈ P.outside,
          (P.glueSeam O).leftFace ⟨C.face, hC⟩ = F) ∨
        ∃ C ∈ Xi.relatorCells, (P.glueSeam O).rightFace ⟨C.face, C.face_ne_outer⟩ = F := by
  unfold glueRelFaces
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ F))

theorem glueOuter_not_mem (O : OEquivalentDiscDiagram P.diagram Xi) :
    (P.glueSeam O).leftFace ⟨Delta.outerFace, P.outerFace_mem⟩ ∉ P.glueRelFaces O := by
  rewrite [P.mem_glueRelFaces O]
  rintro (⟨C, -, hC, hCF⟩ | ⟨C, -, hCF⟩)
  · exact C.face_ne_outer (congrArg Subtype.val ((P.glueSeam O).leftFace_injective hCF))
  · exact (P.glueSeam O).leftFace_ne_rightFace _ _ hCF.symm

theorem glueRelFaces_word (O : OEquivalentDiscDiagram P.diagram Xi) :
    ∀ F ∈ P.glueRelFaces O,
      ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary F).darts.map
        ((P.glueSeam O).glueLabel Delta.label Xi.label) ∈ W := by
  intro F hF
  rcases (P.mem_glueRelFaces O F).1 hF with ⟨C, hC, hCo, rfl⟩ | ⟨C, hC, rfl⟩
  · rewrite [(P.glueSeam O).glueFaceBoundary_leftFace_word Delta.faceBoundary Xi.faceBoundary
      Delta.label Xi.label C.face hCo, ← Delta.relatorCell_word C hC]
    exact C.word_mem
  · rewrite [(P.glueSeam O).glueFaceBoundary_rightFace_word Delta.faceBoundary Xi.faceBoundary
      Delta.label Xi.label C.face C.face_ne_outer, ← Xi.relatorCell_word C hC]
    exact C.word_mem

theorem glueRelFaces_triv (O : OEquivalentDiscDiagram P.diagram Xi) :
    ∀ F, F ≠ (P.glueSeam O).leftFace ⟨Delta.outerFace, P.outerFace_mem⟩ →
      F ∉ P.glueRelFaces O →
        RelLetter.listVal
          (((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary F).darts.map
            ((P.glueSeam O).glueLabel Delta.label Xi.label)) = 1 := by
  intro F hF hnot
  rcases (P.glueSeam O).exists_leftFace_or_rightFace F with ⟨g, hg, rfl⟩ | ⟨h, hh, rfl⟩
  · rewrite [(P.glueSeam O).glueFaceBoundary_leftFace_word Delta.faceBoundary Xi.faceBoundary
      Delta.label Xi.label g hg]
    have hgo : g ≠ Delta.outerFace := fun hgo => hF (by subst hgo; rfl)
    rcases Delta.inner_face g hgo with ⟨C, hC, hCg⟩ | hone
    · subst hCg
      exact absurd ((P.mem_glueRelFaces O _).2 (Or.inl ⟨C, hC, hg, rfl⟩)) hnot
    · exact hone
  · rewrite [(P.glueSeam O).glueFaceBoundary_rightFace_word Delta.faceBoundary Xi.faceBoundary
      Delta.label Xi.label h hh]
    rcases Xi.inner_face h hh with ⟨C, hC, hCh⟩ | hone
    · subst hCh
      exact absurd ((P.mem_glueRelFaces O _).2 (Or.inr ⟨C, hC, rfl⟩)) hnot
    · exact hone

/-- **The glued diagram.**  An O-equivalent copy of the pocket glued into the complement of the
pocket, along a complement cycle that follows the boundary. -/
def glueDiagram (O : OEquivalentDiscDiagram P.diagram Xi) (hwalk : P.outer.FollowsBoundary) :
    DiscDiagram.{u, w, v} W :=
  DiscDiagram.ofPlanar (P.glueSeam O).glueMap
    ((P.glueSeam O).glueMap_planar hwalk Delta.planar Xi.planar)
    ((P.glueSeam O).glueLabel Delta.label Xi.label)
    ((P.glueSeam O).glueLabel_alpha Delta.label Xi.label RelWord.inv Delta.label_alpha
      Xi.label_alpha (P.glueSeam_label O))
    ((P.glueSeam O).leftFace ⟨Delta.outerFace, P.outerFace_mem⟩)
    ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary)
    (P.glueRelFaces O) (P.glueOuter_not_mem O) (P.glueRelFaces_word O) (P.glueRelFaces_triv O)

/-- The glued diagram has the boundary word of `Δ`. -/
theorem glueDiagram_boundaryWord (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) :
    (P.glueDiagram O hwalk).boundaryWord = Delta.boundaryWord :=
  congrArg RelWord.revInv ((P.glueSeam O).glueFaceBoundary_leftFace_word Delta.faceBoundary
    Xi.faceBoundary Delta.label Xi.label Delta.outerFace P.outerFace_mem)

/-- The relator cells of the glued diagram lie exactly on the relator faces. -/
theorem glueDiagram_face_mem_iff (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) (F : (P.glueSeam O).glueMap.Face) :
    F ∈ (P.glueDiagram O hwalk).relatorCells.map RelatorCell.face ↔ F ∈ P.glueRelFaces O :=
  (exists_relatorCells_of_planar (W := W) (P.glueSeam O).glueMap
    ((P.glueSeam O).glueMap_planar hwalk Delta.planar Xi.planar)
    ((P.glueSeam O).glueLabel Delta.label Xi.label)
    ((P.glueSeam O).glueLabel_alpha Delta.label Xi.label RelWord.inv Delta.label_alpha
      Xi.label_alpha (P.glueSeam_label O))
    ((P.glueSeam O).leftFace ⟨Delta.outerFace, P.outerFace_mem⟩)
    ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary)
    (P.glueRelFaces O) (P.glueOuter_not_mem O) (P.glueRelFaces_word O)
    (P.glueRelFaces_triv O)).choose_spec.2.1 F

open scoped Classical in
/-- A face of the copy as a face of the glued map; the outer face of the copy goes to the outer
face. -/
def glueXFace (O : OEquivalentDiscDiagram P.diagram Xi) (h : Xi.toCombMap.Face) :
    (P.glueSeam O).glueMap.Face :=
  if hh : h = Xi.outerFace then (P.glueSeam O).leftFace ⟨Delta.outerFace, P.outerFace_mem⟩
  else (P.glueSeam O).rightFace ⟨h, hh⟩

theorem glueXFace_outer (O : OEquivalentDiscDiagram P.diagram Xi) :
    P.glueXFace O Xi.outerFace = (P.glueSeam O).leftFace ⟨Delta.outerFace, P.outerFace_mem⟩ := by
  unfold glueXFace
  exact dif_pos rfl

theorem glueXFace_of_ne (O : OEquivalentDiscDiagram P.diagram Xi) (h : Xi.toCombMap.Face)
    (hh : h ≠ Xi.outerFace) : P.glueXFace O h = (P.glueSeam O).rightFace ⟨h, hh⟩ := by
  unfold glueXFace
  exact dif_neg hh

theorem glueXFace_injective (O : OEquivalentDiscDiagram P.diagram Xi) :
    Function.Injective (P.glueXFace O) := by
  intro h₁ h₂ heq
  by_cases h1 : h₁ = Xi.outerFace
  · by_cases h2 : h₂ = Xi.outerFace
    · exact h1.trans h2.symm
    · rewrite [h1, P.glueXFace_outer O, P.glueXFace_of_ne O h₂ h2] at heq
      exact absurd heq ((P.glueSeam O).leftFace_ne_rightFace _ _)
  · by_cases h2 : h₂ = Xi.outerFace
    · rewrite [h2, P.glueXFace_outer O, P.glueXFace_of_ne O h₁ h1] at heq
      exact absurd heq.symm ((P.glueSeam O).leftFace_ne_rightFace _ _)
    · rewrite [P.glueXFace_of_ne O h₁ h1, P.glueXFace_of_ne O h₂ h2] at heq
      exact congrArg Subtype.val ((P.glueSeam O).rightFace_injective heq)

/-- **The copy embeds into the glued diagram** away from its outer face. -/
def glueEmbeddingAway (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) :
    DiscEmbeddingAway Xi (P.glueDiagram O hwalk) Xi.outerFace where
  darts := (P.glueSeam O).glueEmbedding
  faces := ⟨P.glueXFace O, P.glueXFace_injective O⟩
  alpha x := (P.glueSeam O).glueAlpha_glueEmbedding x
  label x := (P.glueSeam O).glueLabel_glueEmbedding Delta.label Xi.label (P.glueSeam_label O) x
  outer := (P.glueXFace_outer O).symm
  face_boundary h hh :=
    (congrArg
      (fun F => ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary F).darts)
      (P.glueXFace_of_ne O h hh)).trans
      ((P.glueSeam O).glueFaceBoundary_rightFace_darts Delta.faceBoundary Xi.faceBoundary h hh)
  facePerm x hx := (P.glueSeam O).glueMap_facePerm_glueEmbedding x hx

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.PocketGlue.Seam.exists_leftFace_or_rightFace
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.outerWord_eq_of_oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueSeam_label
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueDiagram
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueDiagram_boundaryWord
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueDiagram_face_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueEmbeddingAway
