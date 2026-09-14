import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueComponents
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketGlueEquivalence
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixLeastAreaCut
import GroupApproximation.GGT.VanKampen.DiscDiagramOfPlanarRestrict
import GroupApproximation.Meta.AxiomGuard

/-!
# The exterior component of a glued copy of a pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b): regions of copies of `Γ_1` glue back into
regions of copies of `Δ`.

Let `P` be a pocket region of `Δ` and `Ξ` an O-equivalent copy of the pocket diagram, glued into the
complement of `P` along its cycle (`PocketRegion.glueSeam`).  When the cycle does not follow the
boundary, the glued map can split.  Take the component of the exterior face, planar by
`PocketGlueComponentPlanarStatement`: it is a disc diagram with the boundary word of `Δ`.  Its
relator cells are the relator faces it meets, and the glued map has at most as many relator faces
as `Δ` has relator cells.  So when `Δ` is least area, the component meets every relator face, and
it is O-equivalent to `Δ`.

* `DiscDiagram.ofPlanarRestrict_face_mem_iff`: the relator faces of a planar piece.
* `PocketRegion.componentDiagram`: the exterior component as a disc diagram.
* `PocketRegion.componentDiagram_boundaryWord`: it has the boundary word of `Δ`.
* `PocketRegion.card_glueRelFaces_le`: the glued map has at most `rCellCount Δ` relator faces.
* `PocketRegion.exists_componentOf_of_mem_glueRelFaces`: at least area, the exterior component
  meets every relator face.
* `PocketRegion.componentOEquivalent`: at least area, it is O-equivalent to `Δ`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, through Osin's Lemma 9.7(b)); certifies no printed
sentence on its own.
-/

noncomputable section

namespace GroupApproximation.GGT.VanKampen

open HullSC Surgery.MapCollapse Surgery.PocketGlue

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The relator faces of the disc diagram on a planar piece** are the faces of the piece carried
by relator faces. -/
theorem DiscDiagram.ofPlanarRestrict_face_mem_iff {W : Set (List (RelLetter G Lambda))}
    (M : CombMap.{v}) (S : M.Dart → Prop) (hα : ∀ x, S (M.alpha x) ↔ S x)
    (hσ : ∀ x, S (M.sigma x) ↔ S x) (hplanar : (M.restrict S hα hσ).IsPlanar)
    (label : M.Dart → RelLetter G Lambda)
    (label_alpha : ∀ d, label (M.alpha d) = RelWord.inv (label d))
    (faceBoundary : ∀ f, FaceBoundary M f) (relFaces : Finset M.Face) (o : M.Dart) (ho : S o)
    (houter : M.faceOf o ∉ relFaces)
    (hword : ∀ f ∈ relFaces, (faceBoundary f).darts.map label ∈ W)
    (htriv : ∀ d, S d → M.faceOf d ≠ M.faceOf o → M.faceOf d ∉ relFaces →
      RelLetter.listVal ((faceBoundary (M.faceOf d)).darts.map label) = 1)
    (F : (M.restrict S hα hσ).Face) :
    F ∈ (DiscDiagram.ofPlanarRestrict (W := W) M S hα hσ hplanar label label_alpha faceBoundary
      relFaces o ho houter hword htriv).relatorCells.map RelatorCell.face ↔
        M.restrictFace S hα hσ F ∈ relFaces := by
  refine ((exists_relatorCells_of_planar (W := W) (M.restrict S hα hσ) hplanar
    (fun x => label x.1) (fun x => label_alpha x.1) ((M.restrict S hα hσ).faceOf ⟨o, ho⟩)
    (M.restrictFaceBoundary S hα hσ faceBoundary) (M.restrictRelFaces S hα hσ relFaces)
    (M.restrictRelFaces_outer_not_mem S hα hσ relFaces o ho houter)
    (M.restrictRelFaces_word S hα hσ faceBoundary label relFaces hword)
    (M.restrictRelFaces_triv S hα hσ faceBoundary label relFaces o ho htriv)).choose_spec.2.1
      F).trans ?_
  simp only [CombMap.restrictRelFaces, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The relator faces of a disc diagram are as many as its relator cells. -/
theorem DiscDiagram.nat_card_relatorFaces {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) :
    Nat.card {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face} =
      Delta.rCellCount := by
  rw [← Nat.card_congr (cellFaceEquiv Delta), Nat.card_eq_fintype_card, Fintype.card_fin]

namespace PocketRegion

variable {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  (P : PocketRegion Delta) {Xi : DiscDiagram.{u, w, v} W}

/-- A dart of the exterior face of `Δ`, as a dart of the glued map. -/
def glueOuterDart (O : OEquivalentDiscDiagram P.diagram Xi) : (P.glueSeam O).glueMap.Dart :=
  (P.glueSeam O).faceDart ((Delta.faceBoundary Delta.outerFace).darts.head
      (Delta.faceBoundary Delta.outerFace).nonempty)
    ((P.glueSeam O).faceOf_mem_of_mem_darts Delta.outerFace P.outerFace_mem
      (Delta.faceBoundary Delta.outerFace) _ (List.head_mem _))

theorem glueMap_faceOf_glueOuterDart (O : OEquivalentDiscDiagram P.diagram Xi) :
    (P.glueSeam O).glueMap.faceOf (P.glueOuterDart O) =
      (P.glueSeam O).leftFace ⟨Delta.outerFace, P.outerFace_mem⟩ :=
  ((P.glueSeam O).faceOf_inl _).trans (congrArg (P.glueSeam O).leftFace (Subtype.ext
    (((Delta.faceBoundary Delta.outerFace).mem_iff _).mp (List.head_mem _))))

theorem glueOuterDart_not_mem (O : OEquivalentDiscDiagram P.diagram Xi) :
    (P.glueSeam O).glueMap.faceOf (P.glueOuterDart O) ∉ P.glueRelFaces O := by
  rw [P.glueMap_faceOf_glueOuterDart O]
  exact P.glueOuter_not_mem O

theorem glueRelFaces_triv_component (O : OEquivalentDiscDiagram P.diagram Xi) :
    ∀ d, (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) d →
      (P.glueSeam O).glueMap.faceOf d ≠ (P.glueSeam O).glueMap.faceOf (P.glueOuterDart O) →
        (P.glueSeam O).glueMap.faceOf d ∉ P.glueRelFaces O →
          RelLetter.listVal (((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary
            ((P.glueSeam O).glueMap.faceOf d)).darts.map
              ((P.glueSeam O).glueLabel Delta.label Xi.label)) = 1 :=
  fun _ _ hne hnot =>
    P.glueRelFaces_triv O _ (by rwa [P.glueMap_faceOf_glueOuterDart O] at hne) hnot

/-- **The exterior component of the glued map as a disc diagram**, given that it is planar. -/
def componentDiagram (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar) :
    DiscDiagram.{u, w, v} W :=
  DiscDiagram.ofPlanarRestrict (P.glueSeam O).glueMap
    ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
    ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
    ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O)) hplanar
    ((P.glueSeam O).glueLabel Delta.label Xi.label)
    ((P.glueSeam O).glueLabel_alpha Delta.label Xi.label RelWord.inv Delta.label_alpha
      Xi.label_alpha (P.glueSeam_label O))
    ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary) (P.glueRelFaces O)
    (P.glueOuterDart O) ((P.glueSeam O).glueMap.componentOf_self (P.glueOuterDart O))
    (P.glueOuterDart_not_mem O) (P.glueRelFaces_word O) (P.glueRelFaces_triv_component O)

/-- The exterior component has the boundary word of `Δ`. -/
theorem componentDiagram_boundaryWord (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar) :
    (P.componentDiagram O hplanar).boundaryWord = Delta.boundaryWord := by
  have hw := (P.glueSeam O).glueFaceBoundary_leftFace_word Delta.faceBoundary Xi.faceBoundary
    Delta.label Xi.label Delta.outerFace P.outerFace_mem
  rw [← P.glueMap_faceOf_glueOuterDart O] at hw
  unfold componentDiagram
  rw [DiscDiagram.ofPlanarRestrict_boundaryWord]
  exact congrArg RelWord.revInv hw

/-- The relator faces of the exterior component are the faces carried by relator faces. -/
theorem componentDiagram_face_mem_iff (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (F : (P.componentDiagram O hplanar).toCombMap.Face) :
    F ∈ (P.componentDiagram O hplanar).relatorCells.map RelatorCell.face ↔
      (P.glueSeam O).glueMap.restrictFace
        ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
        ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
        ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O)) F ∈ P.glueRelFaces O :=
  DiscDiagram.ofPlanarRestrict_face_mem_iff (W := W) (P.glueSeam O).glueMap
    ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
    ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
    ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O)) hplanar
    ((P.glueSeam O).glueLabel Delta.label Xi.label)
    ((P.glueSeam O).glueLabel_alpha Delta.label Xi.label RelWord.inv Delta.label_alpha
      Xi.label_alpha (P.glueSeam_label O))
    ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary) (P.glueRelFaces O)
    (P.glueOuterDart O) ((P.glueSeam O).glueMap.componentOf_self (P.glueOuterDart O))
    (P.glueOuterDart_not_mem O) (P.glueRelFaces_word O) (P.glueRelFaces_triv_component O) F

open scoped Classical in
/-- The relator cells of the exterior component are the relator faces it meets. -/
theorem componentDiagram_rCellCount (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar) :
    (P.componentDiagram O hplanar).rCellCount =
      ((P.glueRelFaces O).filter fun F => ∃ d,
        (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) d ∧
          (P.glueSeam O).glueMap.faceOf d = F).card :=
  DiscDiagram.ofPlanarRestrict_rCellCount (W := W) (P.glueSeam O).glueMap
    ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
    ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
    ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O)) hplanar
    ((P.glueSeam O).glueLabel Delta.label Xi.label)
    ((P.glueSeam O).glueLabel_alpha Delta.label Xi.label RelWord.inv Delta.label_alpha
      Xi.label_alpha (P.glueSeam_label O))
    ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary) (P.glueRelFaces O)
    (P.glueOuterDart O) ((P.glueSeam O).glueMap.componentOf_self (P.glueOuterDart O))
    (P.glueOuterDart_not_mem O) (P.glueRelFaces_word O) (P.glueRelFaces_triv_component O)

/-! ## Relator faces of the glued map -/

theorem glueLeft_mem_glueRelFaces (O : OEquivalentDiscDiagram P.diagram Xi)
    {g : Delta.toCombMap.Face} (hg : g ∈ Delta.relatorCells.map RelatorCell.face)
    (hgo : g ∈ P.outside) : (P.glueSeam O).leftFace ⟨g, hgo⟩ ∈ P.glueRelFaces O := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hg
  exact (P.mem_glueRelFaces O _).2 (Or.inl ⟨C, hC, hgo, rfl⟩)

theorem glueRight_mem_glueRelFaces (O : OEquivalentDiscDiagram P.diagram Xi)
    {h : Xi.toCombMap.Face} (hh : h ∈ Xi.relatorCells.map RelatorCell.face) :
    (P.glueSeam O).rightFace ⟨h, DiscDiagram.relFace_ne_outerFace hh⟩ ∈ P.glueRelFaces O := by
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hh
  exact (P.mem_glueRelFaces O _).2 (Or.inr ⟨C, hC, rfl⟩)

open scoped Classical in
/-- A relator face of `Δ` as a relator face of the glued map: a face outside the pocket stays, and
a face inside goes to its matched face of the copy. -/
def glueRelFace (O : OEquivalentDiscDiagram P.diagram Xi)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face}) :
    {F : (P.glueSeam O).glueMap.Face // F ∈ P.glueRelFaces O} :=
  if hf : f.1 ∈ P.outside then
    ⟨(P.glueSeam O).leftFace ⟨f.1, hf⟩, P.glueLeft_mem_glueRelFaces O f.2 hf⟩
  else
    ⟨(P.glueSeam O).rightFace
        ⟨(P.keptImage O f hf).1, DiscDiagram.relFace_ne_outerFace (P.keptImage O f hf).2⟩,
      P.glueRight_mem_glueRelFaces O (P.keptImage O f hf).2⟩

theorem glueRelFace_of_mem (O : OEquivalentDiscDiagram P.diagram Xi)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face})
    (hf : f.1 ∈ P.outside) : (P.glueRelFace O f).1 = (P.glueSeam O).leftFace ⟨f.1, hf⟩ := by
  unfold glueRelFace
  rw [dif_pos hf]

theorem glueRelFace_of_not_mem (O : OEquivalentDiscDiagram P.diagram Xi)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face})
    (hf : f.1 ∉ P.outside) :
    (P.glueRelFace O f).1 = (P.glueSeam O).rightFace
      ⟨(P.keptImage O f hf).1, DiscDiagram.relFace_ne_outerFace (P.keptImage O f hf).2⟩ := by
  unfold glueRelFace
  rw [dif_neg hf]

/-- The matching preserves the face words. -/
theorem glueRelFace_word (O : OEquivalentDiscDiagram P.diagram Xi)
    (f : {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face}) :
    ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary
        (P.glueRelFace O f).1).darts.map ((P.glueSeam O).glueLabel Delta.label Xi.label) =
      Delta.faceWord f.1 := by
  by_cases hf : f.1 ∈ P.outside
  · rw [P.glueRelFace_of_mem O f hf]
    exact (P.glueSeam O).glueFaceBoundary_leftFace_word Delta.faceBoundary Xi.faceBoundary
      Delta.label Xi.label f.1 hf
  · rw [P.glueRelFace_of_not_mem O f hf]
    exact ((P.glueSeam O).glueFaceBoundary_rightFace_word Delta.faceBoundary Xi.faceBoundary
      Delta.label Xi.label _ (DiscDiagram.relFace_ne_outerFace (P.keptImage O f hf).2)).trans
      ((O.faceWord_faceEquiv
          ⟨keptFace Delta.toCombMap P.outside P.outer f.1 hf, P.kept_mem f.2 hf⟩).trans
        (replaceGRegionFaceBoundary_keptFace_word Delta P.outside P.outer f.1 hf))

theorem glueRelFace_surjective (O : OEquivalentDiscDiagram P.diagram Xi) :
    Function.Surjective (P.glueRelFace O) := by
  intro F
  rcases (P.mem_glueRelFaces O F.1).1 F.2 with ⟨C, hC, hCo, hCF⟩ | ⟨C, hC, hCF⟩
  · refine ⟨⟨C.face, List.mem_map_of_mem hC⟩, Subtype.ext ?_⟩
    exact (P.glueRelFace_of_mem O ⟨C.face, List.mem_map_of_mem hC⟩ hCo).trans hCF
  · obtain ⟨k, hk⟩ := O.faceEquiv.surjective ⟨C.face, List.mem_map_of_mem hC⟩
    obtain ⟨g, hgo, hg, hgk⟩ := P.exists_of_mem_cellFaces ((P.diagram_face_mem_iff k.1).1 k.2)
    refine ⟨⟨g, hg⟩, Subtype.ext ?_⟩
    have hkk : P.keptImage O ⟨g, hg⟩ hgo = ⟨C.face, List.mem_map_of_mem hC⟩ :=
      (congrArg (fun x => O.faceEquiv x)
        (Subtype.ext hgk : (⟨keptFace Delta.toCombMap P.outside P.outer g hgo, P.kept_mem hg hgo⟩ :
          {F : P.diagram.toCombMap.Face // F ∈ P.diagram.relatorCells.map RelatorCell.face}) =
            k)).trans hk
    exact (P.glueRelFace_of_not_mem O ⟨g, hg⟩ hgo).trans
      ((congrArg (fun x : {h : Xi.toCombMap.Face // h ∈ Xi.relatorCells.map RelatorCell.face} =>
        (P.glueSeam O).rightFace ⟨x.1, DiscDiagram.relFace_ne_outerFace x.2⟩) hkk).trans hCF)

/-- **The glued map has at most as many relator faces as `Δ` has relator cells.** -/
theorem card_glueRelFaces_le (O : OEquivalentDiscDiagram P.diagram Xi) :
    (P.glueRelFaces O).card ≤ Delta.rCellCount := by
  have h := Nat.card_le_card_of_surjective _ (P.glueRelFace_surjective O)
  rwa [Nat.card_eq_finsetCard, DiscDiagram.nat_card_relatorFaces] at h

/-- At least area, `Δ` has at most as many relator cells as the exterior component. -/
theorem rCellCount_le_componentDiagram (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) : Delta.rCellCount ≤ (P.componentDiagram O hplanar).rCellCount := by
  have hval : (P.componentDiagram O hplanar).boundaryValue = Delta.boundaryValue :=
    congrArg RelLetter.listVal (P.componentDiagram_boundaryWord O hplanar)
  have hprod := (P.componentDiagram O hplanar).isRelatorProduct_boundaryValue
  rw [hval] at hprod
  exact hlea hprod

/-- **At least area, the exterior component meets every relator face.** -/
theorem exists_componentOf_of_mem_glueRelFaces (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) {F : (P.glueSeam O).glueMap.Face} (hF : F ∈ P.glueRelFaces O) :
    ∃ d, (P.glueSeam O).glueMap.componentOf (P.glueOuterDart O) d ∧
      (P.glueSeam O).glueMap.faceOf d = F := by
  classical
  have hY := P.componentDiagram_rCellCount O hplanar
  have hle := P.rCellCount_le_componentDiagram O hplanar hlea
  have hcard := P.card_glueRelFaces_le O
  exact Finset.filter_card_eq (le_antisymm (Finset.card_filter_le _ _)
    (hcard.trans (hle.trans hY.le))) F hF

theorem card_glueRelFaces_eq (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) : (P.glueRelFaces O).card = Delta.rCellCount := by
  classical
  have hY := P.componentDiagram_rCellCount O hplanar
  have hle := P.rCellCount_le_componentDiagram O hplanar hlea
  exact le_antisymm (P.card_glueRelFaces_le O) (hle.trans (hY.le.trans (Finset.card_filter_le _ _)))

/-- At least area, the relator faces of `Δ` and of the glued map, matched. -/
def glueRelFaceEquiv (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) :
    {f : Delta.toCombMap.Face // f ∈ Delta.relatorCells.map RelatorCell.face} ≃
      {F : (P.glueSeam O).glueMap.Face // F ∈ P.glueRelFaces O} :=
  Equiv.ofBijective (P.glueRelFace O) ((Nat.bijective_iff_surjective_and_card _).mpr
    ⟨P.glueRelFace_surjective O, by
      rw [DiscDiagram.nat_card_relatorFaces, Nat.card_eq_finsetCard]
      exact (P.card_glueRelFaces_eq O hplanar hlea).symm⟩)

/-- A relator face of the exterior component as a relator face of the glued map. -/
def componentRelFace (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (F : {F : (P.componentDiagram O hplanar).toCombMap.Face //
      F ∈ (P.componentDiagram O hplanar).relatorCells.map RelatorCell.face}) :
    {F : (P.glueSeam O).glueMap.Face // F ∈ P.glueRelFaces O} :=
  ⟨(P.glueSeam O).glueMap.restrictFace ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
      ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
      ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O)) F.1,
    (P.componentDiagram_face_mem_iff O hplanar F.1).mp F.2⟩

/-- At least area, the relator faces of the exterior component and of the glued map, matched. -/
def componentRelFaceEquiv (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) :
    {F : (P.componentDiagram O hplanar).toCombMap.Face //
      F ∈ (P.componentDiagram O hplanar).relatorCells.map RelatorCell.face} ≃
      {F : (P.glueSeam O).glueMap.Face // F ∈ P.glueRelFaces O} :=
  Equiv.ofBijective (P.componentRelFace O hplanar)
    ⟨fun F₁ F₂ h => Subtype.ext ((P.glueSeam O).glueMap.restrictFace_injective _ _ _
      (congrArg Subtype.val h)), by
      rintro ⟨F, hF⟩
      obtain ⟨d, hd, rfl⟩ := P.exists_componentOf_of_mem_glueRelFaces O hplanar hlea hF
      exact ⟨⟨((P.glueSeam O).glueMap.component (P.glueOuterDart O)).faceOf ⟨d, hd⟩,
        (P.componentDiagram_face_mem_iff O hplanar _).mpr hF⟩, rfl⟩⟩

/-- **At least area, the exterior component is O-equivalent to `Δ`.** -/
def componentOEquivalent (O : OEquivalentDiscDiagram P.diagram Xi)
    (hplanar : ((P.glueSeam O).glueMap.component (P.glueOuterDart O)).IsPlanar)
    (hlea : Delta.LeastArea) : OEquivalentDiscDiagram Delta (P.componentDiagram O hplanar) :=
  OEquivalentDiscDiagram.ofCellFaceEquiv (P.componentDiagram_boundaryWord O hplanar)
    ((P.glueRelFaceEquiv O hplanar hlea).trans (P.componentRelFaceEquiv O hplanar hlea).symm)
    (fun f => by
      have h : (P.glueSeam O).glueMap.restrictFace
          ((P.glueSeam O).glueMap.componentOf (P.glueOuterDart O))
          ((P.glueSeam O).glueMap.componentOf_alpha (P.glueOuterDart O))
          ((P.glueSeam O).glueMap.componentOf_sigma (P.glueOuterDart O))
          (((P.glueRelFaceEquiv O hplanar hlea).trans
            (P.componentRelFaceEquiv O hplanar hlea).symm) f).1 = (P.glueRelFace O f).1 :=
        congrArg Subtype.val ((P.componentRelFaceEquiv O hplanar hlea).apply_symm_apply _)
      exact ((P.glueSeam O).glueMap.restrictFaceBoundary_word _ _ _
        ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary)
        ((P.glueSeam O).glueLabel Delta.label Xi.label) _).trans
        ((congrArg (fun F => ((P.glueSeam O).glueFaceBoundary Delta.faceBoundary Xi.faceBoundary
          F).darts.map ((P.glueSeam O).glueLabel Delta.label Xi.label)) h).trans
          (P.glueRelFace_word O f)))

end PocketRegion

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.ofPlanarRestrict_face_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.componentDiagram_boundaryWord
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.card_glueRelFaces_le
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.exists_componentOf_of_mem_glueRelFaces
#audit_axioms GroupApproximation.GGT.VanKampen.PocketRegion.componentOEquivalent
