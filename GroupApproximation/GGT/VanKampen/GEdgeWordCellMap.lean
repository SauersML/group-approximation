import GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision
import GroupApproximation.GGT.VanKampen.SurgeryCellMap

/-!
# Actual arbitrary word subdivision retaining the complete ordered cell data

The stronger producer performs the same relabelling and subdivision recursion.
Each actual step preserves words, individual conjugators and orientations, and
composition retains the exact ordered relator-cell list.
-/

namespace GroupApproximation.GGT.VanKampen

open HullSC EdgeSubdivision
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

namespace GEdgeRelabel

noncomputable def orderedCellMap (Delta : DiscDiagram.{u, w, v} W)
    (a : Delta.toCombMap.Dart) (letter : RelLetter G Lambda)
    (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
    (hvalue : letter.val = (Delta.label a).val) :
    Surgery.OrderedRCellMap Delta (diagram Delta a letter houter hcells hvalue)
      (expansion Delta a letter houter hcells hvalue).faceEquiv where
  cell := id
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := (List.map_id _).symm

end GEdgeRelabel

namespace GEdgeSubdivision

noncomputable def orderedCellMap (Delta : DiscDiagram.{u, w, v} W)
    (a : Delta.toCombMap.Dart)
    (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
    (left right : RelLetter G Lambda)
    (hfactor : (Delta.label a).val = left.val * right.val) :
    Surgery.OrderedRCellMap Delta (diagram Delta a houter hcells left right hfactor)
      (expansion Delta a houter hcells left right hfactor).faceEquiv where
  cell := cell Delta a
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

end GEdgeSubdivision

namespace GEdgeWordSubdivision

/-- The actual subdivision geometry and exact words, before imposing
legality on all labels elsewhere in the diagram. -/
structure RawOutput (Delta : DiscDiagram.{u, w, v} W)
    (a : Delta.toCombMap.Dart) (word : List (RelLetter G Lambda)) where
  diagram : DiscDiagram.{u, w, v} W
  expansion : DiscExpansion Delta diagram
  word_eq : (expansion.darts a).map diagram.label = word
  other_word : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a →
    (expansion.darts d).map diagram.label = [Delta.label d]
  cells : Surgery.OrderedRCellMap Delta diagram expansion.faceEquiv

structure CellOutput (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (a : Delta.toCombMap.Dart) (word : List (RelLetter G Lambda))
    extends Output D Delta a word where
  cells : Surgery.OrderedRCellMap Delta diagram expansion.faceEquiv

/-- Subdivide the edge into an arbitrary nonempty word of the same value.
All other edges retain their exact single-letter words. -/
theorem exists_raw_output
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (Delta : DiscDiagram.{u, w, v} W) (a : Delta.toCombMap.Dart)
    (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
    (hvalue : RelLetter.listVal word = (Delta.label a).val) :
    Nonempty (RawOutput Delta a word) := by
  classical
  induction word generalizing Delta with
  | nil => exact (hne rfl).elim
  | cons letter tail ih =>
      by_cases htail : tail = []
      · subst tail
        have hv : letter.val = (Delta.label a).val := by simpa [RelLetter.listVal] using hvalue
        refine ⟨{
          diagram := GEdgeRelabel.diagram Delta a letter houter hcells hv
          expansion := GEdgeRelabel.expansion Delta a letter houter hcells hv
          cells := GEdgeRelabel.orderedCellMap Delta a letter houter hcells hv
          word_eq := ?_
          other_word := ?_ }⟩
        · change [GEdgeRelabel.label Delta a letter a] = [letter]
          exact congrArg List.singleton (GEdgeRelabel.label_at Delta a letter)
        · intro d ha hb
          change [GEdgeRelabel.label Delta a letter d] = [Delta.label d]
          exact congrArg List.singleton (GEdgeRelabel.label_other Delta a letter d ha hb)
      · let right : RelLetter G Lambda := .base (RelLetter.listVal tail)
        have hfactor : (Delta.label a).val = letter.val * right.val := by
          exact hvalue.symm.trans (RelWord.listVal_cons letter tail)
        let Xi := GEdgeSubdivision.diagram Delta a houter hcells letter right hfactor
        let b : Xi.toCombMap.Dart := embed Delta.toCombMap a
        have hbvalue : RelLetter.listVal tail = (Xi.label b).val :=
          (congrArg RelLetter.val
            (GEdgeSubdivision.remaining_label Delta a houter hcells letter right hfactor)).symm
        obtain ⟨R⟩ := ih htail Xi b
          (GEdgeSubdivision.remaining_outer Delta a houter)
          (GEdgeSubdivision.remaining_cells Delta a houter hcells letter right hfactor) hbvalue
        let E := GEdgeSubdivision.expansion Delta a houter hcells letter right hfactor
        let expandR : EdgeSubdivision.Dart Delta.toCombMap → List R.diagram.toCombMap.Dart := R.expansion.darts
        refine ⟨{
          diagram := R.diagram
          expansion := E.trans R.expansion
          cells := (GEdgeSubdivision.orderedCellMap Delta a houter hcells letter right hfactor).trans R.cells
          word_eq := ?_
          other_word := ?_ }⟩
        · change ((expand Delta.toCombMap a a).flatMap expandR).map R.diagram.label = _
          have hexpand : expand Delta.toCombMap a a = [none, embed Delta.toCombMap a] := by simp [expand]
          rw [hexpand, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
          have hfirst := R.other_word (none : Xi.toCombMap.Dart)
            (by change (none : EdgeSubdivision.Dart Delta.toCombMap) ≠ some (some a); intro h; cases h)
            (by change (none : EdgeSubdivision.Dart Delta.toCombMap) ≠ some (some (Delta.toCombMap.alpha a)); intro h; cases h)
          exact (congrArg₂ List.append hfirst R.word_eq).trans rfl
        · intro d ha hb
          change ((expand Delta.toCombMap a d).flatMap expandR).map R.diagram.label = _
          have hexpand : expand Delta.toCombMap a d = [embed Delta.toCombMap d] := by simp [expand, ha, hb]
          rw [hexpand, List.flatMap_singleton]
          have hda : embed Delta.toCombMap d ≠ b := by
            intro h
            exact ha (Option.some.inj (Option.some.inj h))
          have hdb : embed Delta.toCombMap d ≠ Xi.toCombMap.alpha b := by
            intro h
            exact hb (Option.some.inj (Option.some.inj h))
          refine (R.other_word (embed Delta.toCombMap d) hda hdb).trans ?_
          change [subdivideLabel Delta.toCombMap a Delta.label letter right (embed Delta.toCombMap d)] = [Delta.label d]
          simp only [subdivideLabel, embed, EdgeInsertion.embed, if_neg ha, if_neg hb]

/-- The geometry covers every new dart, so local word legality plus legality
of untouched old edges gives legality of the whole output. -/
theorem RawOutput.label_admissible (D : RelGenSet G Lambda)
    {Delta : DiscDiagram.{u, w, v} W} {a : Delta.toCombMap.Dart}
    {word : List (RelLetter G Lambda)} (R : RawOutput Delta a word)
    (hword : ∀ l ∈ word, D.IsLetter l)
    (hinv : ∀ l ∈ word, D.IsLetter (RelWord.inv l))
    (hlabel : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a → D.IsLetter (Delta.label d))
    (x : R.diagram.toCombMap.Dart) : D.IsLetter (R.diagram.label x) := by
  obtain ⟨d, hd⟩ := R.expansion.exists_old_dart x
  have hx : R.diagram.label x ∈ (R.expansion.darts d).map R.diagram.label :=
    List.mem_map.mpr ⟨x, hd, rfl⟩
  by_cases ha : d = a
  · subst d
    rw [R.word_eq] at hx
    exact hword _ hx
  · by_cases hb : d = Delta.toCombMap.alpha a
    · subst d
      rw [R.expansion.word_alpha, R.word_eq] at hx
      obtain ⟨l, hl, hleq⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
      rw [← hleq]
      exact hinv l hl
    · rw [R.other_word d ha hb] at hx
      rw [List.mem_singleton.mp hx]
      exact hlabel d ha hb

/-- Only the inserted word and its formal inverse need be legal. No
inverse-closure hypothesis on the whole base alphabet is required. -/
theorem exists_cell_output_of_reversible (D : RelGenSet G Lambda)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (hinv : ∀ letter ∈ word, D.IsLetter (RelWord.inv letter))
    (Delta : DiscDiagram.{u, w, v} W) (a : Delta.toCombMap.Dart)
    (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
    (hlabel : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a → D.IsLetter (Delta.label d))
    (hvalue : RelLetter.listVal word = (Delta.label a).val) :
    Nonempty (CellOutput D Delta a word) := by
  obtain ⟨R⟩ := exists_raw_output word hne Delta a houter hcells hvalue
  exact ⟨{
    diagram := R.diagram
    expansion := R.expansion
    word_eq := R.word_eq
    other_word := R.other_word
    cells := R.cells
    label_admissible := R.label_admissible D hword hinv hlabel }⟩

theorem exists_cell_output (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (Delta : DiscDiagram.{u, w, v} W) (a : Delta.toCombMap.Dart)
    (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
    (hlabel : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a → D.IsLetter (Delta.label d))
    (hvalue : RelLetter.listVal word = (Delta.label a).val) :
    Nonempty (CellOutput D Delta a word) :=
  exists_cell_output_of_reversible D word hne hword
    (fun l hl => isLetter_relWordInv D hsymm (hword l hl)) Delta a houter hcells hlabel hvalue

end GEdgeWordSubdivision
end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeRelabel.orderedCellMap
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeSubdivision.orderedCellMap
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.exists_cell_output
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.exists_cell_output_of_reversible
#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.exists_raw_output
