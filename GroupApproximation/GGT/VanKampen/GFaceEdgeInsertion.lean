import GroupApproximation.GGT.VanKampen.CombMapEdgeLabels
import GroupApproximation.GGT.VanKampen.CombMapEdgePlanarity
import GroupApproximation.GGT.VanKampen.SurgeryOrderedCells

/-!
# Inserting a labelled edge across an actual G-face

The new planar disc and every face traversal are constructed. Its relator
cells retain their words, order, conjugators and orientation. The exterior
word is exact, and the repaired actual-list transport proves reducedness and
O-equivalence. The chosen letter must represent the boundary prefix: this is
the one-edge operation, before general connector-path subdivision.
-/

namespace GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion

open HullSC EdgeInsertion Surgery
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (k : Fin (Delta.faceBoundary f).darts.length)

noncomputable abbrev map : CombMap.{v} := splitMap Delta.toCombMap (Delta.faceBoundary f) k

noncomputable abbrev keep (g : Delta.toCombMap.Face) : (map Delta f k).Face :=
  keptFace Delta.toCombMap (firstCorner Delta.toCombMap (Delta.faceBoundary f))
    (secondCorner Delta.toCombMap (Delta.faceBoundary f) k) g

theorem keep_injective : Function.Injective (keep Delta f k) :=
  keptFace_injective Delta.toCombMap _ _ (corners_face_eq Delta.toCombMap (Delta.faceBoundary f) k)

noncomputable def cell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (map Delta f k) (keep Delta f k Delta.outerFace) W where
  face := keep Delta f k C.face
  face_ne_outer := fun h => C.face_ne_outer (keep_injective Delta f k h)
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

theorem cells_faces_nodup :
    ((Delta.relatorCells.map (cell Delta f k)).map RelatorCell.face).Nodup := by
  have heq : (Delta.relatorCells.map (cell Delta f k)).map RelatorCell.face =
      (Delta.relatorCells.map RelatorCell.face).map (keep Delta f k) := by
    rw [List.map_map, List.map_map]
    rfl
  rw [heq]
  exact Delta.relatorCell_faces_nodup.map (keep_injective Delta f k)

theorem gFace_value (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f) :
    RelLetter.listVal ((Delta.faceBoundary f).darts.map Delta.label) = 1 := by
  rcases Delta.inner_face f hf with ⟨C, hC, heq⟩ | hval
  · exact (hcells C hC heq).elim
  · exact hval

noncomputable def diagram (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    DiscDiagram.{u, w, v} W where
  toCombMap := map Delta f k
  planar := planar Delta.toCombMap _ _ Delta.planar
    (corners_face_eq Delta.toCombMap (Delta.faceBoundary f) k)
  label := insertLabel Delta.toCombMap Delta.label letter
  label_alpha := insertLabel_alpha Delta.toCombMap Delta.label Delta.label_alpha letter _ _
  outerFace := keep Delta f k Delta.outerFace
  faceBoundary := allFaceBoundary Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary k
  relatorCells := Delta.relatorCells.map (cell Delta f k)
  relatorCell_faces_nodup := cells_faces_nodup Delta f k
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    exact (Delta.relatorCell_word C₀ hC₀).trans
      (split_kept_word Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary k
        C₀.face (hcells C₀ hC₀) Delta.label letter).symm
  inner_face := by
    intro F hF
    rcases face_partition Delta.toCombMap (Delta.faceBoundary f) k F with hpre | hsuf | ⟨g, hg, hkept⟩
    · right
      rw [hpre]
      exact split_prefix_null Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary k
        Delta.label letter hprefix
    · right
      rw [hsuf]
      exact split_suffix_null Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary k
        Delta.label letter hprefix (gFace_value Delta f hf hcells)
    · have hgo : g ≠ Delta.outerFace := by
        intro h
        exact hF (hkept.trans (congrArg (keep Delta f k) h))
      rcases Delta.inner_face g hgo with ⟨C, hC, hCg⟩ | hval
      · left
        refine ⟨cell Delta f k C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        exact (congrArg (keep Delta f k) hCg).trans hkept.symm
      · right
        rw [hkept]
        exact (congrArg RelLetter.listVal
          (split_kept_word Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary k
            g hg Delta.label letter)).trans hval
  boundary_product := by
    have hvalues : (Delta.relatorCells.map (cell Delta f k)).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    exact (congrArg List.prod hvalues).trans (Delta.boundary_product.trans
      (congrArg (fun word => RelLetter.listVal (RelWord.revInv word))
        (split_kept_word Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary k
          Delta.outerFace hf.symm Delta.label letter).symm))

theorem boundaryWord_eq (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    (diagram Delta f k hf hcells letter hprefix).boundaryWord = Delta.boundaryWord := by
  apply congrArg RelWord.revInv
  exact split_kept_word Delta.toCombMap (Delta.faceBoundary f) Delta.faceBoundary k
    Delta.outerFace hf.symm Delta.label letter

theorem orderedCells (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    OrderedRCellTransport Delta (diagram Delta f k hf hcells letter hprefix) := by
  constructor
  · change (Delta.relatorCells.map (cell Delta f k)).map RelatorCell.word = _
    rw [List.map_map]
    rfl
  · change (Delta.relatorCells.map (cell Delta f k)).map RelatorCell.value = _
    rw [List.map_map]
    rfl

/-- The constructed local surgery supplies the corrected replacement record. -/
noncomputable def replacement (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    OrderedGRegionReplacement.{u, w, v, v} Delta where
  diagram := diagram Delta f k hf hcells letter hprefix
  outerWord_eq := boundaryWord_eq Delta f k hf hcells letter hprefix
  cells := orderedCells Delta f k hf hcells letter hprefix

theorem reduced (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label))
    (hred : Delta.Reduced) : (diagram Delta f k hf hcells letter hprefix).Reduced :=
  (replacement Delta f k hf hcells letter hprefix).reduced hred

theorem faceCount_eq (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label)) :
    (diagram Delta f k hf hcells letter hprefix).toCombMap.faceCount = Delta.toCombMap.faceCount + 1 :=
  EdgeInsertion.faceCount_eq Delta.toCombMap _ _ (corners_face_eq Delta.toCombMap (Delta.faceBoundary f) k)

theorem label_admissible (hf : f ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ f)
    (letter : RelLetter G Lambda)
    (hprefix : letter.val = RelLetter.listVal (((Delta.faceBoundary f).darts.take k.val).map Delta.label))
    (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) (hletter : D.IsLetter letter)
    (d : (diagram Delta f k hf hcells letter hprefix).toCombMap.Dart) :
    D.IsLetter ((diagram Delta f k hf hcells letter hprefix).label d) :=
  insertLabel_admissible Delta.toCombMap D hsymm Delta.label hlabel letter hletter d

end GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.boundaryWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.replacement
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.faceCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceEdgeInsertion.label_admissible
