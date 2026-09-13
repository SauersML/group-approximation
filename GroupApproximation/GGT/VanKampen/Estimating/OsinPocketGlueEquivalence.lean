import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueDiagram
import GroupApproximation.GGT.VanKampen.OEquivalentCellFaces
import GroupApproximation.Meta.AxiomGuard

/-!
# The glued diagram is O-equivalent to the diagram

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): gluing an O-equivalent copy of the pocket
back into the diagram gives an O-equivalent copy of the diagram.

Let `P` be a pocket region of `Δ` and `Ξ` an O-equivalent copy of the pocket diagram, glued back
along a complement cycle that follows the boundary (`PocketRegion.glueDiagram`).  A relator face
of `Δ` outside the pocket stays a relator face of the glued diagram.  A relator face inside the
pocket is a kept face of the pocket diagram, and the O-equivalence matches it to a relator face
of `Ξ`, which is again a relator face of the glued diagram.  This matching is a bijection
preserving the face words, and the glued diagram has the boundary word of `Δ`.

* `PocketRegion.diagram_face_mem_iff`: the relator faces of the pocket diagram.
* `PocketRegion.glueCellFaceEquiv`: the relator faces of `Δ` and of the glued diagram, matched.
* `PocketRegion.glueOEquivalent`: the glued diagram is O-equivalent to `Δ`.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v

/-- A relator face is not the outer face. -/
theorem DiscDiagram.relFace_ne_outerFace {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (RelLetter G Lambda))} {Xi : DiscDiagram.{u, w, v} W} {h : Xi.toCombMap.Face}
    (hh : h ∈ Xi.relatorCells.map RelatorCell.face) : h ≠ Xi.outerFace := by
  obtain ⟨C, -, rfl⟩ := List.mem_map.1 hh
  exact C.face_ne_outer

namespace PocketRegion

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} (P : PocketRegion Delta) {Xi : DiscDiagram.{u, w, v} W}

/-- The relator cells of the pocket diagram lie exactly on `cellFaces`. -/
theorem diagram_face_mem_iff (F : (replaceGRegion Delta.toCombMap P.outside P.outer).Face) :
    F ∈ P.diagram.relatorCells.map RelatorCell.face ↔ F ∈ P.cellFaces :=
  (exists_relatorCells_of_planar (W := W) (replaceGRegion Delta.toCombMap P.outside P.outer)
    (replaceGRegion_planar Delta.toCombMap P.outside P.outer Delta.planar)
    (fun d => Delta.label d.1) (fun d => Delta.label_alpha d.1)
    (newFace Delta.toCombMap P.outside P.outer)
    (replaceGRegionFaceBoundary Delta.toCombMap P.outside P.outer Delta.faceBoundary)
    P.cellFaces P.newFace_not_mem_cellFaces P.cellFaces_word_mem
    P.cellFaces_triv).choose_spec.2.1 F

open scoped Classical in
/-- A relator face of `Δ` inside the pocket is a relator face of the pocket diagram. -/
theorem kept_mem {g : Delta.toCombMap.Face} (hg : g ∈ Delta.relatorCells.map RelatorCell.face)
    (hgo : g ∉ P.outside) :
    keptFace Delta.toCombMap P.outside P.outer g hgo ∈
      P.diagram.relatorCells.map RelatorCell.face := by
  refine (P.diagram_face_mem_iff _).2 ?_
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hg
  unfold cellFaces
  rw [List.mem_toFinset]
  exact List.mem_map.mpr ⟨C, List.mem_filter.mpr
    ⟨hC, by simpa using P.mem_faces_of_not_mem_outside hgo⟩, dif_neg hgo⟩

open scoped Classical in
/-- Every relator face of the pocket diagram is the kept face of a relator face of `Δ` inside
the pocket. -/
theorem exists_of_mem_cellFaces {F : (replaceGRegion Delta.toCombMap P.outside P.outer).Face}
    (hF : F ∈ P.cellFaces) :
    ∃ g, ∃ hg : g ∉ P.outside, g ∈ Delta.relatorCells.map RelatorCell.face ∧
      keptFace Delta.toCombMap P.outside P.outer g hg = F := by
  unfold cellFaces at hF
  rw [List.mem_toFinset] at hF
  obtain ⟨C, hC, hCF⟩ := List.mem_map.mp hF
  have hC' := List.mem_filter.mp hC
  have hCout : C.face ∉ P.outside := P.not_mem_outside (by simpa using hC'.2)
  simp only [dif_neg hCout] at hCF
  exact ⟨C.face, hCout, List.mem_map_of_mem hC'.1, hCF⟩

/-- A relator face of `Δ` outside the pocket is a relator face of the glued diagram. -/
theorem glueLeft_mem (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) {g : Delta.toCombMap.Face}
    (hg : g ∈ Delta.relatorCells.map RelatorCell.face) (hgo : g ∈ P.outside) :
    (P.glueSeam O).leftFace ⟨g, hgo⟩ ∈
      (P.glueDiagram O hwalk).relatorCells.map RelatorCell.face := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hg
  exact (P.glueDiagram_face_mem_iff O hwalk _).2
    ((P.mem_glueRelFaces O _).2 (Or.inl ⟨C, hC, hgo, rfl⟩))

/-- A relator face of the copy is a relator face of the glued diagram. -/
theorem glueRight_mem (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) {h : Xi.toCombMap.Face}
    (hh : h ∈ Xi.relatorCells.map RelatorCell.face) :
    (P.glueSeam O).rightFace ⟨h, DiscDiagram.relFace_ne_outerFace hh⟩ ∈
      (P.glueDiagram O hwalk).relatorCells.map RelatorCell.face := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hh
  exact (P.glueDiagram_face_mem_iff O hwalk _).2
    ((P.mem_glueRelFaces O _).2 (Or.inr ⟨C, hC, rfl⟩))

/-- The relator face of the copy matched to a relator face of `Δ` inside the pocket. -/
def keptImage (O : OEquivalentDiscDiagram P.diagram Xi)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face})
    (hf : f.1 ∉ P.outside) :
    {h : Xi.toCombMap.Face // h ∈ Xi.relatorCells.map RelatorCell.face} :=
  O.faceEquiv ⟨keptFace Delta.toCombMap P.outside P.outer f.1 hf, P.kept_mem f.2 hf⟩

open scoped Classical in
/-- A relator face of `Δ` as a relator face of the glued diagram: a face outside the pocket
stays, and a face inside goes to its matched face of the copy. -/
def glueCellFace (O : OEquivalentDiscDiagram P.diagram Xi) (hwalk : P.outer.FollowsBoundary)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face}) :
    {F : (P.glueDiagram O hwalk).toCombMap.Face //
      F ∈ (P.glueDiagram O hwalk).relatorCells.map RelatorCell.face} :=
  if hf : f.1 ∈ P.outside then
    ⟨(P.glueSeam O).leftFace ⟨f.1, hf⟩, P.glueLeft_mem O hwalk f.2 hf⟩
  else
    ⟨(P.glueSeam O).rightFace
        ⟨(P.keptImage O f hf).1, DiscDiagram.relFace_ne_outerFace (P.keptImage O f hf).2⟩,
      P.glueRight_mem O hwalk (P.keptImage O f hf).2⟩

theorem glueCellFace_of_mem (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face})
    (hf : f.1 ∈ P.outside) :
    (P.glueCellFace O hwalk f).1 = (P.glueSeam O).leftFace ⟨f.1, hf⟩ := by
  unfold glueCellFace
  rw [dif_pos hf]

theorem glueCellFace_of_not_mem (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face})
    (hf : f.1 ∉ P.outside) :
    (P.glueCellFace O hwalk f).1 = (P.glueSeam O).rightFace
      ⟨(P.keptImage O f hf).1, DiscDiagram.relFace_ne_outerFace (P.keptImage O f hf).2⟩ := by
  unfold glueCellFace
  rw [dif_neg hf]

/-- The matching preserves the face words. -/
theorem glueCellFace_word (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face}) :
    (P.glueDiagram O hwalk).faceWord (P.glueCellFace O hwalk f).1 = Delta.faceWord f.1 := by
  by_cases hf : f.1 ∈ P.outside
  · rw [P.glueCellFace_of_mem O hwalk f hf]
    exact (P.glueSeam O).glueFaceBoundary_leftFace_word Delta.faceBoundary Xi.faceBoundary
      Delta.label Xi.label f.1 hf
  · rw [P.glueCellFace_of_not_mem O hwalk f hf]
    exact ((P.glueSeam O).glueFaceBoundary_rightFace_word Delta.faceBoundary Xi.faceBoundary
      Delta.label Xi.label _ (DiscDiagram.relFace_ne_outerFace (P.keptImage O f hf).2)).trans
      ((O.faceWord_faceEquiv
          ⟨keptFace Delta.toCombMap P.outside P.outer f.1 hf, P.kept_mem f.2 hf⟩).trans
        (replaceGRegionFaceBoundary_keptFace_word Delta P.outside P.outer f.1 hf))

theorem glueCellFace_injective (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) : Function.Injective (P.glueCellFace O hwalk) := by
  intro f₁ f₂ heq
  have hval := congrArg Subtype.val heq
  by_cases h1 : f₁.1 ∈ P.outside
  · by_cases h2 : f₂.1 ∈ P.outside
    · have h := (P.glueCellFace_of_mem O hwalk f₁ h1).symm.trans
        (hval.trans (P.glueCellFace_of_mem O hwalk f₂ h2))
      exact Subtype.ext (congrArg Subtype.val ((P.glueSeam O).leftFace_injective h))
    · exact absurd ((P.glueCellFace_of_mem O hwalk f₁ h1).symm.trans
        (hval.trans (P.glueCellFace_of_not_mem O hwalk f₂ h2)))
        ((P.glueSeam O).leftFace_ne_rightFace _ _)
  · by_cases h2 : f₂.1 ∈ P.outside
    · exact absurd ((P.glueCellFace_of_mem O hwalk f₂ h2).symm.trans
        (hval.symm.trans (P.glueCellFace_of_not_mem O hwalk f₁ h1)))
        ((P.glueSeam O).leftFace_ne_rightFace _ _)
    · have h := (P.glueCellFace_of_not_mem O hwalk f₁ h1).symm.trans
        (hval.trans (P.glueCellFace_of_not_mem O hwalk f₂ h2))
      have hk : (⟨keptFace Delta.toCombMap P.outside P.outer f₁.1 h1, P.kept_mem f₁.2 h1⟩ :
            {F : P.diagram.toCombMap.Face // F ∈ P.diagram.relatorCells.map RelatorCell.face}) =
          ⟨keptFace Delta.toCombMap P.outside P.outer f₂.1 h2, P.kept_mem f₂.2 h2⟩ :=
        O.faceEquiv.injective
          (Subtype.ext (congrArg Subtype.val ((P.glueSeam O).rightFace_injective h)))
      exact Subtype.ext
        (keptFace_inj Delta.toCombMap P.outside P.outer f₁.1 f₂.1 h1 h2 (congrArg Subtype.val hk))

theorem glueCellFace_surjective (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) : Function.Surjective (P.glueCellFace O hwalk) := by
  intro F
  rcases (P.mem_glueRelFaces O F.1).1 ((P.glueDiagram_face_mem_iff O hwalk F.1).1 F.2) with
    ⟨C, hC, hCo, hCF⟩ | ⟨C, hC, hCF⟩
  · refine ⟨⟨C.face, List.mem_map_of_mem hC⟩, Subtype.ext ?_⟩
    exact (P.glueCellFace_of_mem O hwalk ⟨C.face, List.mem_map_of_mem hC⟩ hCo).trans hCF
  · obtain ⟨k, hk⟩ := O.faceEquiv.surjective ⟨C.face, List.mem_map_of_mem hC⟩
    obtain ⟨g, hgo, hg, hgk⟩ := P.exists_of_mem_cellFaces ((P.diagram_face_mem_iff k.1).1 k.2)
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    have hkk : P.keptImage O ⟨g, hg⟩ hgo = ⟨C.face, List.mem_map_of_mem hC⟩ :=
      (congrArg (fun x => O.faceEquiv x)
        (Subtype.ext hgk : (⟨keptFace Delta.toCombMap P.outside P.outer g hgo, P.kept_mem hg hgo⟩ :
          {F : P.diagram.toCombMap.Face // F ∈ P.diagram.relatorCells.map RelatorCell.face}) =
            k)).trans hk
    exact (P.glueCellFace_of_not_mem O hwalk ⟨g, hg⟩ hgo).trans
      ((congrArg (fun x : {h : Xi.toCombMap.Face // h ∈ Xi.relatorCells.map RelatorCell.face} =>
        (P.glueSeam O).rightFace ⟨x.1, DiscDiagram.relFace_ne_outerFace x.2⟩) hkk).trans hCF)

/-- The relator faces of `Δ` and of the glued diagram, matched. -/
def glueCellFaceEquiv (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) :
    {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face} ≃
      {F : (P.glueDiagram O hwalk).toCombMap.Face //
        F ∈ (P.glueDiagram O hwalk).relatorCells.map RelatorCell.face} :=
  Equiv.ofBijective (P.glueCellFace O hwalk)
    ⟨P.glueCellFace_injective O hwalk, P.glueCellFace_surjective O hwalk⟩

/-- **The glued diagram is O-equivalent to `Δ`.** -/
def glueOEquivalent (O : OEquivalentDiscDiagram P.diagram Xi)
    (hwalk : P.outer.FollowsBoundary) : OEquivalentDiscDiagram Delta (P.glueDiagram O hwalk) :=
  OEquivalentDiscDiagram.ofCellFaceEquiv (P.glueDiagram_boundaryWord O hwalk)
    (P.glueCellFaceEquiv O hwalk) (P.glueCellFace_word O hwalk)

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.relFace_ne_outerFace
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.diagram_face_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.kept_mem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_of_mem_cellFaces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueLeft_mem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueRight_mem
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueCellFace_word
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueCellFaceEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.glueOEquivalent
