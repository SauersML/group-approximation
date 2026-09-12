import GroupApproximation.GGT.VanKampen.PendantEdgeWalks
import GroupApproximation.GGT.VanKampen.DiscDiagram
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# A disc diagram with a pendant edge attached at an outer corner

A new edge reading `letter` outward is attached before an exterior dart `b`.
The old labels, face words, relator cells and conjugators are kept.  Every
face word is expanded letter by letter; only the exterior word changes, by the
cancelling pair `letter letter⁻¹` read just before `b`, so its value is
unchanged and the stored product formula carries over.

* `diagram`: the new disc diagram.
* `boundaryValue_eq`, `rCellCount_eq`: the exterior value and the relator area
  are unchanged.
* `outerDarts_eq`: the exterior traversal is the expanded old one.
* `cell_cover`: relator coverage of the inner faces is preserved.
-/

namespace GroupApproximation.GGT.VanKampen.PendantEdge

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (b : Delta.toCombMap.Dart) (letter : RelLetter G Lambda)

noncomputable local instance : DecidableEq Delta.toCombMap.Dart := Classical.decEq _

/-- Labels of the map with a pendant edge: the new edge reads `letter` outward. -/
def pendantLabel : EdgeInsertion.Dart Delta.toCombMap → RelLetter G Lambda
  | none => HullSC.RelWord.inv letter
  | some none => letter
  | some (some d) => Delta.label d

theorem pendantLabel_alpha (x : EdgeInsertion.Dart Delta.toCombMap) :
    pendantLabel Delta letter ((toCombMap Delta.toCombMap b).alpha x) =
      HullSC.RelWord.inv (pendantLabel Delta letter x) := by
  rcases x with _ | (_ | d)
  · exact (HullSC.RelWord.inv_inv_letter letter).symm
  · rfl
  · exact Delta.label_alpha d

theorem expand_word_of_ne (d : Delta.toCombMap.Dart) (hd : d ≠ b) :
    (expand Delta.toCombMap b d).map (pendantLabel Delta letter) = [Delta.label d] := by
  have h : expand Delta.toCombMap b d = [some (some d)] := if_neg hd
  rw [h]
  rfl

theorem expand_word_self :
    (expand Delta.toCombMap b b).map (pendantLabel Delta letter) =
      [letter, HullSC.RelWord.inv letter, Delta.label b] := by
  have h : expand Delta.toCombMap b b = [some none, none, some (some b)] := if_pos rfl
  rw [h]
  rfl

/-- A face walk avoiding `b` reads its old word. -/
theorem expanded_word_kept (l : List Delta.toCombMap.Dart) (hb : b ∉ l) :
    (l.flatMap (expand Delta.toCombMap b)).map (pendantLabel Delta letter) =
      l.map Delta.label := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      have hd : d ≠ b := fun h => hb (by rw [← h]; exact List.mem_cons_self)
      have hl : b ∉ l := fun h => hb (List.mem_cons_of_mem d h)
      simp only [List.flatMap_cons, List.map_append, expand_word_of_ne Delta b letter d hd,
        ih hl, List.map_cons, List.singleton_append]

/-- **Every expanded face walk has its old value.** -/
theorem expanded_word_value (l : List Delta.toCombMap.Dart) :
    RelLetter.listVal ((l.flatMap (expand Delta.toCombMap b)).map (pendantLabel Delta letter)) =
      RelLetter.listVal (l.map Delta.label) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      rw [List.flatMap_cons, List.map_append, HullSC.RelWord.listVal_append, ih, List.map_cons,
        HullSC.RelWord.listVal_cons]
      by_cases hd : d = b
      · rw [hd, expand_word_self, HullSC.RelWord.listVal_cons, HullSC.RelWord.listVal_cons,
          HullSC.RelWord.listVal_singleton, HullSC.RelWord.val_inv, mul_inv_cancel_left]
      · rw [expand_word_of_ne Delta b letter d hd, HullSC.RelWord.listVal_singleton]

/-- A relator cell of the new diagram. -/
noncomputable def cell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (toCombMap Delta.toCombMap b)
      ((faceEquiv Delta.toCombMap b).symm Delta.outerFace) W where
  face := (faceEquiv Delta.toCombMap b).symm C.face
  face_ne_outer := fun h => C.face_ne_outer ((faceEquiv Delta.toCombMap b).symm.injective h)
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

theorem cells_faces_nodup :
    ((Delta.relatorCells.map (cell Delta b)).map RelatorCell.face).Nodup := by
  have heq : (Delta.relatorCells.map (cell Delta b)).map RelatorCell.face =
      (Delta.relatorCells.map RelatorCell.face).map (faceEquiv Delta.toCombMap b).symm := by
    rw [List.map_map, List.map_map]
    rfl
  rw [heq]
  exact Delta.relatorCell_faces_nodup.map (faceEquiv Delta.toCombMap b).symm.injective

variable (houter : Delta.toCombMap.faceOf b = Delta.outerFace)

include houter in
/-- The corner dart lies on no relator face. -/
theorem not_mem_cell_boundary (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    b ∉ (Delta.faceBoundary C.face).darts := by
  intro hb
  have h := ((Delta.faceBoundary C.face).mem_iff b).mp hb
  exact C.face_ne_outer (h.symm.trans houter)

include houter in
/-- **The diagram with a pendant edge attached at an outer corner.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := toCombMap Delta.toCombMap b
  planar := planar Delta.toCombMap b Delta.planar
  label := pendantLabel Delta letter
  label_alpha := pendantLabel_alpha Delta b letter
  outerFace := (faceEquiv Delta.toCombMap b).symm Delta.outerFace
  faceBoundary := allBoundary Delta.toCombMap b Delta.faceBoundary
  relatorCells := Delta.relatorCells.map (cell Delta b)
  relatorCell_faces_nodup := cells_faces_nodup Delta b
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    change C₀.word = (allBoundary Delta.toCombMap b Delta.faceBoundary
      ((faceEquiv Delta.toCombMap b).symm C₀.face)).darts.map (pendantLabel Delta letter)
    rw [allBoundary_darts,
      expanded_word_kept Delta b letter _ (not_mem_cell_boundary Delta b houter C₀)]
    exact Delta.relatorCell_word C₀ hC₀
  inner_face := by
    intro F hF
    have hgo : faceEquiv Delta.toCombMap b F ≠ Delta.outerFace := by
      intro h
      apply hF
      rw [← h, Equiv.symm_apply_apply]
    rcases Delta.inner_face (faceEquiv Delta.toCombMap b F) hgo with ⟨C, hC, hCg⟩ | hval
    · left
      refine ⟨cell Delta b C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
      change (faceEquiv Delta.toCombMap b).symm C.face = F
      rw [hCg, Equiv.symm_apply_apply]
    · right
      have hF' : F = (faceEquiv Delta.toCombMap b).symm (faceEquiv Delta.toCombMap b F) :=
        ((faceEquiv Delta.toCombMap b).symm_apply_apply F).symm
      rw [hF', allBoundary_darts, expanded_word_value]
      exact hval
  boundary_product := by
    have hvalues : (Delta.relatorCells.map (cell Delta b)).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    rw [hvalues, Delta.boundary_product, HullSC.RelWord.listVal_revInv,
      HullSC.RelWord.listVal_revInv,
      show (allBoundary Delta.toCombMap b Delta.faceBoundary
          ((faceEquiv Delta.toCombMap b).symm Delta.outerFace)).darts =
        (Delta.faceBoundary Delta.outerFace).darts.flatMap (expand Delta.toCombMap b) from
        allBoundary_darts Delta.toCombMap b Delta.faceBoundary Delta.outerFace,
      expanded_word_value]

/-- The exterior traversal of the new diagram is the expanded old one. -/
theorem outerDarts_eq :
    ((diagram Delta b letter houter).faceBoundary (diagram Delta b letter houter).outerFace).darts =
      (Delta.faceBoundary Delta.outerFace).darts.flatMap (expand Delta.toCombMap b) :=
  allBoundary_darts Delta.toCombMap b Delta.faceBoundary Delta.outerFace

/-- **The exterior value is unchanged.** -/
theorem boundaryValue_eq :
    (diagram Delta b letter houter).boundaryValue = Delta.boundaryValue := by
  change RelLetter.listVal (HullSC.RelWord.revInv
      ((allBoundary Delta.toCombMap b Delta.faceBoundary
        ((faceEquiv Delta.toCombMap b).symm Delta.outerFace)).darts.map
          (pendantLabel Delta letter))) =
    RelLetter.listVal (HullSC.RelWord.revInv
      ((Delta.faceBoundary Delta.outerFace).darts.map Delta.label))
  rw [HullSC.RelWord.listVal_revInv, HullSC.RelWord.listVal_revInv, allBoundary_darts,
    expanded_word_value]

/-- **The relator area is unchanged.** -/
theorem rCellCount_eq : (diagram Delta b letter houter).rCellCount = Delta.rCellCount := by
  show (Delta.relatorCells.map (cell Delta b)).length = Delta.relatorCells.length
  exact List.length_map _

/-- **Relator coverage of the inner faces is preserved.** -/
theorem cell_cover
    (hcover : ∀ f, f ≠ Delta.outerFace → ∃ C ∈ Delta.relatorCells, C.face = f) :
    ∀ F, F ≠ (diagram Delta b letter houter).outerFace →
      ∃ C ∈ (diagram Delta b letter houter).relatorCells, C.face = F := by
  intro F hF
  have hgo : faceEquiv Delta.toCombMap b F ≠ Delta.outerFace := by
    intro h
    apply hF
    change F = (faceEquiv Delta.toCombMap b).symm Delta.outerFace
    rw [← h, Equiv.symm_apply_apply]
  obtain ⟨C, hC, hCg⟩ := hcover _ hgo
  refine ⟨cell Delta b C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
  change (faceEquiv Delta.toCombMap b).symm C.face = F
  rw [hCg, Equiv.symm_apply_apply]

end GroupApproximation.GGT.VanKampen.PendantEdge

#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.pendantLabel_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.expanded_word_value
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.boundaryValue_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.rCellCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PendantEdge.cell_cover
