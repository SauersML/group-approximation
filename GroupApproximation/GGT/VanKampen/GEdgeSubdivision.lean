import GroupApproximation.GGT.VanKampen.CombMapSubdivisionLabels
import GroupApproximation.GGT.VanKampen.SurgeryOrderedCells

/-!
# Subdivide an actual interior G-edge in a labelled disc

Both darts must avoid the exterior and every listed relator face. Their
incident G-faces need not be distinct. The actual map, all boundary walks,
labels and ordered relator cells are constructed. Label factorization
preserves based face values, including a face meeting both orientations.
-/

namespace GroupApproximation.GGT.VanKampen.GEdgeSubdivision

open HullSC EdgeSubdivision Surgery
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (a : Delta.toCombMap.Dart)

noncomputable abbrev map : CombMap.{v} := EdgeSubdivision.toCombMap Delta.toCombMap a

noncomputable abbrev keep : Delta.toCombMap.Face ≃ (map Delta a).Face :=
  (faceEquiv Delta.toCombMap a).symm

noncomputable def cell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (map Delta a) (keep Delta a Delta.outerFace) W where
  face := keep Delta a C.face
  face_ne_outer := fun h => C.face_ne_outer ((keep Delta a).injective h)
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

theorem cells_faces_nodup :
    ((Delta.relatorCells.map (cell Delta a)).map RelatorCell.face).Nodup := by
  have heq : (Delta.relatorCells.map (cell Delta a)).map RelatorCell.face =
      (Delta.relatorCells.map RelatorCell.face).map (keep Delta a) := by
    rw [List.map_map, List.map_map]
    rfl
  rw [heq]
  exact Delta.relatorCell_faces_nodup.map (keep Delta a).injective

variable (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
  (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
  (left right : RelLetter G Lambda)
  (hfactor : (Delta.label a).val = left.val * right.val)

noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := map Delta a
  planar := EdgeSubdivision.planar Delta.toCombMap a Delta.planar
  label := subdivideLabel Delta.toCombMap a Delta.label left right
  label_alpha := subdivideLabel_alpha Delta.toCombMap a Delta.label left right Delta.label_alpha
  outerFace := keep Delta a Delta.outerFace
  faceBoundary := allBoundary Delta.toCombMap a Delta.faceBoundary
  relatorCells := Delta.relatorCells.map (cell Delta a)
  relatorCell_faces_nodup := cells_faces_nodup Delta a
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    exact (Delta.relatorCell_word C₀ hC₀).trans
      (allBoundary_word_kept Delta.toCombMap a Delta.label left right Delta.faceBoundary
        C₀.face (hcells C₀ hC₀).1 (hcells C₀ hC₀).2).symm
  inner_face := by
    intro F hF
    have hgo : faceEquiv Delta.toCombMap a F ≠ Delta.outerFace := by
      intro h
      apply hF
      apply (faceEquiv Delta.toCombMap a).injective
      exact h.trans ((faceEquiv Delta.toCombMap a).apply_symm_apply Delta.outerFace).symm
    rcases Delta.inner_face (faceEquiv Delta.toCombMap a F) hgo with ⟨C, hC, hCg⟩ | hval
    · left
      refine ⟨cell Delta a C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
      change keep Delta a C.face = F
      apply (faceEquiv Delta.toCombMap a).injective
      exact ((faceEquiv Delta.toCombMap a).apply_symm_apply C.face).trans hCg
    · right
      exact (expanded_word_value Delta.toCombMap a Delta.label left right Delta.label_alpha hfactor
        (Delta.faceBoundary (faceEquiv Delta.toCombMap a F)).darts).trans hval
  boundary_product := by
    have hvalues : (Delta.relatorCells.map (cell Delta a)).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    exact (congrArg List.prod hvalues).trans (Delta.boundary_product.trans
      (congrArg (fun word => RelLetter.listVal (RelWord.revInv word))
        (allBoundary_word_kept Delta.toCombMap a Delta.label left right Delta.faceBoundary
          Delta.outerFace houter.1 houter.2).symm))

theorem boundaryWord_eq :
    (diagram Delta a houter hcells left right hfactor).boundaryWord = Delta.boundaryWord := by
  apply congrArg RelWord.revInv
  exact allBoundary_word_kept Delta.toCombMap a Delta.label left right Delta.faceBoundary
    Delta.outerFace houter.1 houter.2

theorem orderedCells : OrderedRCellTransport Delta (diagram Delta a houter hcells left right hfactor) := by
  constructor
  · change (Delta.relatorCells.map (cell Delta a)).map RelatorCell.word = _
    rw [List.map_map]
    rfl
  · change (Delta.relatorCells.map (cell Delta a)).map RelatorCell.value = _
    rw [List.map_map]
    rfl

noncomputable def replacement : OrderedGRegionReplacement.{u, w, v, v} Delta where
  diagram := diagram Delta a houter hcells left right hfactor
  outerWord_eq := boundaryWord_eq Delta a houter hcells left right hfactor
  cells := orderedCells Delta a houter hcells left right hfactor

theorem reduced (hred : Delta.Reduced) : (diagram Delta a houter hcells left right hfactor).Reduced :=
  (replacement Delta a houter hcells left right hfactor).reduced hred

theorem faceCount_eq :
    (diagram Delta a houter hcells left right hfactor).toCombMap.faceCount = Delta.toCombMap.faceCount :=
  EdgeSubdivision.faceCount_eq Delta.toCombMap a

theorem label_admissible (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a → D.IsLetter (Delta.label d))
    (hleft : D.IsLetter left) (hright : D.IsLetter right)
    (d : (diagram Delta a houter hcells left right hfactor).toCombMap.Dart) :
    D.IsLetter ((diagram Delta a houter hcells left right hfactor).label d) :=
  subdivideLabel_admissible Delta.toCombMap a Delta.label left right D hsymm hlabel hleft hright d

end GroupApproximation.GGT.VanKampen.GEdgeSubdivision

#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeSubdivision.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeSubdivision.replacement
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeSubdivision.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeSubdivision.label_admissible
