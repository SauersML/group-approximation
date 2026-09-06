import GroupApproximation.GGT.VanKampen.CombMapSubdivisionLabels
import GroupApproximation.GGT.VanKampen.DiscExpansion

/-!
# Changing the spelling of one interior G-edge

A single desired relative letter can replace a temporary product letter of
the same value. This changes no dart, face or path length. Both sides avoid
the exterior and the listed relator faces, whose words remain literal.
-/

namespace GroupApproximation.GGT.VanKampen.GEdgeRelabel

open HullSC EdgeSubdivision
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (a : Delta.toCombMap.Dart)
  (letter : RelLetter G Lambda)

noncomputable def label (d : Delta.toCombMap.Dart) : RelLetter G Lambda :=
  subdivideLabel Delta.toCombMap a Delta.label letter letter (embed Delta.toCombMap d)

theorem label_alpha (d : Delta.toCombMap.Dart) :
    label Delta a letter (Delta.toCombMap.alpha d) = RelWord.inv (label Delta a letter d) :=
  subdivideLabel_alpha Delta.toCombMap a Delta.label letter letter Delta.label_alpha (embed Delta.toCombMap d)

theorem label_at : label Delta a letter a = letter := by
  classical
  simp [label, subdivideLabel, embed, EdgeInsertion.embed]

theorem label_other (d : Delta.toCombMap.Dart) (ha : d ≠ a) (hb : d ≠ Delta.toCombMap.alpha a) :
    label Delta a letter d = Delta.label d := by
  classical
  simp [label, subdivideLabel, embed, EdgeInsertion.embed, ha, hb]

theorem label_value (hvalue : letter.val = (Delta.label a).val) (d : Delta.toCombMap.Dart) :
    (label Delta a letter d).val = (Delta.label d).val := by
  classical
  by_cases ha : d = a
  · subst d
    exact (congrArg RelLetter.val (label_at Delta a letter)).trans hvalue
  · by_cases hb : d = Delta.toCombMap.alpha a
    · subst d
      rw [label_alpha, RelWord.val_inv, label_at, hvalue, Delta.label_alpha, RelWord.val_inv]
    · exact congrArg RelLetter.val (label_other Delta a letter d ha hb)

theorem word_value (hvalue : letter.val = (Delta.label a).val) (l : List Delta.toCombMap.Dart) :
    RelLetter.listVal (l.map (label Delta a letter)) = RelLetter.listVal (l.map Delta.label) := by
  induction l with
  | nil => rfl
  | cons d l ih =>
      rw [List.map_cons, List.map_cons, RelWord.listVal_cons, RelWord.listVal_cons,
        label_value Delta a letter hvalue, ih]

theorem face_word (f : Delta.toCombMap.Face) (ha : Delta.toCombMap.faceOf a ≠ f)
    (hb : Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ f) :
    (Delta.faceBoundary f).darts.map (label Delta a letter) = (Delta.faceBoundary f).darts.map Delta.label := by
  apply List.map_congr_left
  intro d hd
  apply label_other Delta a letter d
  · intro h
    exact ha (h ▸ ((Delta.faceBoundary f).mem_iff d).mp hd)
  · intro h
    exact hb (h ▸ ((Delta.faceBoundary f).mem_iff d).mp hd)

variable (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
  (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
  (hvalue : letter.val = (Delta.label a).val)

noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := Delta.toCombMap
  planar := Delta.planar
  label := label Delta a letter
  label_alpha := label_alpha Delta a letter
  outerFace := Delta.outerFace
  faceBoundary := Delta.faceBoundary
  relatorCells := Delta.relatorCells
  relatorCell_faces_nodup := Delta.relatorCell_faces_nodup
  relatorCell_word C hC := (Delta.relatorCell_word C hC).trans
    (face_word Delta a letter C.face (hcells C hC).1 (hcells C hC).2).symm
  inner_face f hf := by
    rcases Delta.inner_face f hf with h | h
    · exact Or.inl h
    · exact Or.inr ((word_value Delta a letter hvalue _).trans h)
  boundary_product := Delta.boundary_product.trans
    (congrArg (fun word => RelLetter.listVal (RelWord.revInv word))
      (face_word Delta a letter Delta.outerFace houter.1 houter.2).symm)

noncomputable def expansion : DiscExpansion Delta (diagram Delta a letter houter hcells hvalue) where
  toDartExpansion := DartExpansion.refl Delta.toCombMap
  faceEquiv := Equiv.refl _
  boundary_darts f := by
    change (Delta.faceBoundary f).darts = (Delta.faceBoundary f).darts.flatMap (fun d => [d])
    exact (List.flatMap_singleton' _).symm
  outerFace_eq := rfl
  outerWord_eq := congrArg RelWord.revInv (face_word Delta a letter Delta.outerFace houter.1 houter.2)
  cells := ⟨rfl, rfl⟩
  cellFaces_eq := by
    change Delta.relatorCells.map RelatorCell.face = (Delta.relatorCells.map RelatorCell.face).map id
    exact (List.map_id _).symm

theorem label_admissible (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a → D.IsLetter (Delta.label d))
    (hletter : D.IsLetter letter) (d : Delta.toCombMap.Dart) :
    D.IsLetter (label Delta a letter d) :=
  subdivideLabel_admissible Delta.toCombMap a Delta.label letter letter D hsymm hlabel
    hletter hletter (embed Delta.toCombMap d)

end GroupApproximation.GGT.VanKampen.GEdgeRelabel

#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeRelabel.expansion
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeRelabel.label_admissible
