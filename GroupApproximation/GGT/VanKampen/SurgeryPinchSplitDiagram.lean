import GroupApproximation.GGT.VanKampen.SurgeryPinchSplitMap
import GroupApproximation.GGT.VanKampen.DiscTransport
import GroupApproximation.GGT.VanKampen.SurgeryCellMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Vertex splitting in a disc diagram

Surgery 3 of the proof of Osin's Lemma 9.4, Case 2 (arXiv:math/0411039v3, §9): at a vertex where
two distinct complementary G-faces meet, split the vertex (`PinchSplit.toCombMap`), merging the two
faces into one G-face.  Darts, edge reversal and labels are unchanged, and every other face keeps
its literal enumeration, so the exterior boundary word and every relator cell survive letter for
letter.

An `Input` is two darts at one vertex whose corners lie on distinct faces (`Cycles`), neither of
them the exterior and neither a relator face.

* `kept`: old faces to faces of the split, `kept (faceOf d) = faceOf d` for EVERY dart (`kept_faceOf`);
  the two pinch faces go to `merged` (`kept_leftFace`, `kept_rightFace`, `kept_eq_merged_iff`), every
  other face to a distinct face (`kept_inj`, `kept_ne_merged`), and these are all the faces
  (`face_cases`).
* `diagram`: the split disc diagram, with `faceBoundary_kept_darts` (the old walk of every face off
  the pinch), `faceBoundary_merged_darts` (`alpha x :: ys ++ alpha y :: xs`), `merged_value`,
  `merged_ne_outer`, `merged_not_relatorFace`, `faceCount_add_one`, `vertexCount_eq`.
* `boundaryWord_eq`, `cellMap`, `replacement`, `oEquivalent`, `rCellCount_eq`, `reduced`,
  `label_isLetter`.
-/

namespace GroupApproximation.GGT.VanKampen.PinchSplit

open HullSC

universe u w v

/-- A rotation of a trivial word is trivial. -/
theorem listVal_rotate_eq_one_of_eq_one {G : Type u} [Group G] {Lambda : Type w}
    {word : List (RelLetter G Lambda)} (k : ℕ) (hk : k ≤ word.length)
    (h : RelLetter.listVal word = 1) : RelLetter.listVal (word.rotate k) = 1 := by
  rw [List.rotate_eq_drop_append_take hk]
  have h' : RelLetter.listVal (word.take k ++ word.drop k) = 1 := by
    rw [List.take_append_drop]
    exact h
  change ((word.take k ++ word.drop k).map RelLetter.val).prod = 1 at h'
  change ((word.drop k ++ word.take k).map RelLetter.val).prod = 1
  rw [List.map_append, List.prod_append] at h' ⊢
  exact mul_eq_one_comm.mp h'

/-- Two trivial cyclic products, spliced at their first letters, give a trivial product. -/
theorem prod_splice_eq_one {M : Type u} [Group M] (a b : M) (xs ys : List M)
    (hX : (a :: xs).prod = 1) (hY : (b :: ys).prod = 1) : ((a :: ys) ++ (b :: xs)).prod = 1 := by
  rw [List.prod_cons] at hX hY
  rw [List.prod_append, List.prod_cons, List.prod_cons]
  have hY' : ys.prod * b = 1 := mul_eq_one_comm.mp hY
  calc a * ys.prod * (b * xs.prod) = a * (ys.prod * b) * xs.prod := by simp only [mul_assoc]
    _ = 1 := by rw [hY', mul_one, hX]

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **A pinch between two complementary G-faces**: two darts at one vertex whose corners lie on
distinct faces, neither the exterior and neither a relator face. -/
structure Input (Delta : DiscDiagram.{u, w, v} W) where
  x : Delta.toCombMap.Dart
  y : Delta.toCombMap.Dart
  same_vertex : Delta.toCombMap.sigma.SameCycle x y
  cycles : Cycles Delta.toCombMap x y
  left_ne_outer : Delta.toCombMap.faceOf (Delta.toCombMap.alpha x) ≠ Delta.outerFace
  right_ne_outer : Delta.toCombMap.faceOf (Delta.toCombMap.alpha y) ≠ Delta.outerFace
  left_not_cell : ∀ C ∈ Delta.relatorCells,
    C.face ≠ Delta.toCombMap.faceOf (Delta.toCombMap.alpha x)
  right_not_cell : ∀ C ∈ Delta.relatorCells,
    C.face ≠ Delta.toCombMap.faceOf (Delta.toCombMap.alpha y)

namespace Input

variable {Delta : DiscDiagram.{u, w, v} W} (I : Input Delta)

/-- The face of the corner after `x`. -/
abbrev leftFace : Delta.toCombMap.Face := Delta.toCombMap.faceOf (Delta.toCombMap.alpha I.x)

/-- The face of the corner after `y`. -/
abbrev rightFace : Delta.toCombMap.Face := Delta.toCombMap.faceOf (Delta.toCombMap.alpha I.y)

theorem outer_ne_left : Delta.outerFace ≠ I.leftFace := fun h => I.left_ne_outer h.symm

theorem outer_ne_right : Delta.outerFace ≠ I.rightFace := fun h => I.right_ne_outer h.symm

/-- The left pinch face is a G-face. -/
theorem leftFace_value : RelLetter.listVal (Delta.faceWord I.leftFace) = 1 := by
  rcases Delta.inner_face I.leftFace I.left_ne_outer with ⟨C, hC, hface⟩ | h
  · exact absurd hface (I.left_not_cell C hC)
  · exact h

/-- The right pinch face is a G-face. -/
theorem rightFace_value : RelLetter.listVal (Delta.faceWord I.rightFace) = 1 := by
  rcases Delta.inner_face I.rightFace I.right_ne_outer with ⟨C, hC, hface⟩ | h
  · exact absurd hface (I.right_not_cell C hC)
  · exact h

/-- The enumeration of the left pinch face from its corner reads a trivial word. -/
theorem cycX_value :
    RelLetter.listVal ((Delta.toCombMap.alpha I.x :: I.cycles.xs).map Delta.label) = 1 := by
  obtain ⟨k, hk, hrot⟩ := (Delta.faceBoundary I.leftFace).isFaceCycle.exists_rotate_eq
    I.cycles.cycX (FaceBoundary.faceOf_head _)
  rw [← hrot, List.map_rotate]
  exact listVal_rotate_eq_one_of_eq_one k (by rw [List.length_map]; exact hk) I.leftFace_value

/-- The enumeration of the right pinch face from its corner reads a trivial word. -/
theorem cycY_value :
    RelLetter.listVal ((Delta.toCombMap.alpha I.y :: I.cycles.ys).map Delta.label) = 1 := by
  obtain ⟨k, hk, hrot⟩ := (Delta.faceBoundary I.rightFace).isFaceCycle.exists_rotate_eq
    I.cycles.cycY (FaceBoundary.faceOf_head _)
  rw [← hrot, List.map_rotate]
  exact listVal_rotate_eq_one_of_eq_one k (by rw [List.length_map]; exact hk) I.rightFace_value

/-- **The merged enumeration reads a trivial word.** -/
theorem merged_listVal :
    RelLetter.listVal ((Delta.toCombMap.alpha I.x :: I.cycles.ys ++
      Delta.toCombMap.alpha I.y :: I.cycles.xs).map Delta.label) = 1 := by
  have e : ∀ l : List Delta.toCombMap.Dart, RelLetter.listVal (l.map Delta.label) =
      (l.map fun d => (Delta.label d).val).prod := fun l => by
    change ((l.map Delta.label).map RelLetter.val).prod = _
    rw [List.map_map]
    rfl
  have hX := I.cycX_value
  have hY := I.cycY_value
  rw [e, List.map_cons] at hX hY
  rw [e, List.map_append, List.map_cons, List.map_cons]
  exact prod_splice_eq_one _ _ _ _ hX hY

variable [DecidableEq Delta.toCombMap.Dart]

/-- Old darts on one face lie on one face of the split. -/
theorem faceOf_congr {d e : Delta.toCombMap.Dart}
    (h : Delta.toCombMap.faceOf d = Delta.toCombMap.faceOf e) :
    (toCombMap Delta.toCombMap I.x I.y).faceOf d = (toCombMap Delta.toCombMap I.x I.y).faceOf e := by
  by_cases h₁ : Delta.toCombMap.faceOf e = I.leftFace
  · rw [(I.cycles.faceOf_merged_iff d).mpr (Or.inl (h.trans h₁)),
      (I.cycles.faceOf_merged_iff e).mpr (Or.inl h₁)]
  · by_cases h₂ : Delta.toCombMap.faceOf e = I.rightFace
    · rw [(I.cycles.faceOf_merged_iff d).mpr (Or.inr (h.trans h₂)),
        (I.cycles.faceOf_merged_iff e).mpr (Or.inr h₂)]
    · exact (faceOf_eq_iff_of_avoid Delta.toCombMap I.x I.y h₁ h₂ d).mpr h

/-- **Old faces to faces of the split.** -/
def kept : Delta.toCombMap.Face → (toCombMap Delta.toCombMap I.x I.y).Face :=
  Quotient.lift (fun d => (toCombMap Delta.toCombMap I.x I.y).faceOf d)
    (fun d e h => I.faceOf_congr ((Delta.toCombMap.faceOf_eq_iff d e).mpr h))

theorem kept_faceOf (d : Delta.toCombMap.Dart) :
    I.kept (Delta.toCombMap.faceOf d) = (toCombMap Delta.toCombMap I.x I.y).faceOf d := rfl

/-- The merged face. -/
def merged : (toCombMap Delta.toCombMap I.x I.y).Face :=
  (toCombMap Delta.toCombMap I.x I.y).faceOf (Delta.toCombMap.alpha I.x)

theorem kept_leftFace : I.kept I.leftFace = I.merged := rfl

theorem kept_rightFace : I.kept I.rightFace = I.merged := I.cycles.faceOf_alpha_right

theorem kept_eq_merged_iff (g : Delta.toCombMap.Face) :
    I.kept g = I.merged ↔ g = I.leftFace ∨ g = I.rightFace := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep g
  exact I.cycles.faceOf_merged_iff d

theorem kept_ne_merged {g : Delta.toCombMap.Face} (hg₁ : g ≠ I.leftFace)
    (hg₂ : g ≠ I.rightFace) : I.kept g ≠ I.merged :=
  fun h => ((I.kept_eq_merged_iff g).mp h).elim hg₁ hg₂

/-- **Faces off the pinch stay distinct.** -/
theorem kept_inj {g h : Delta.toCombMap.Face} (hg₁ : g ≠ I.leftFace) (hg₂ : g ≠ I.rightFace)
    (heq : I.kept g = I.kept h) : g = h := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep g
  obtain ⟨e, rfl⟩ := Quotient.exists_rep h
  exact ((faceOf_eq_iff_of_avoid Delta.toCombMap I.x I.y hg₁ hg₂ e).mp heq.symm).symm

/-- **Every face of the split is the merged face or a kept face off the pinch.** -/
theorem face_cases (F : (toCombMap Delta.toCombMap I.x I.y).Face) :
    F = I.merged ∨ ∃ g, g ≠ I.leftFace ∧ g ≠ I.rightFace ∧ F = I.kept g := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep F
  by_cases h₁ : Delta.toCombMap.faceOf d = I.leftFace
  · exact Or.inl ((I.cycles.faceOf_merged_iff d).mpr (Or.inl h₁))
  · by_cases h₂ : Delta.toCombMap.faceOf d = I.rightFace
    · exact Or.inl ((I.cycles.faceOf_merged_iff d).mpr (Or.inr h₂))
    · exact Or.inr ⟨Delta.toCombMap.faceOf d, h₁, h₂, rfl⟩

/-- The image of a face other than the old exterior is not the image of the exterior. -/
theorem kept_ne_kept_outer {g : Delta.toCombMap.Face} (hg : g ≠ Delta.outerFace) :
    I.kept g ≠ I.kept Delta.outerFace := by
  intro h
  by_cases h₁ : g = I.leftFace
  · have hm : I.kept g = I.merged := by rw [h₁]; rfl
    exact I.kept_ne_merged I.outer_ne_left I.outer_ne_right (h.symm.trans hm)
  · by_cases h₂ : g = I.rightFace
    · have hm : I.kept g = I.merged := by rw [h₂]; exact I.kept_rightFace
      exact I.kept_ne_merged I.outer_ne_left I.outer_ne_right (h.symm.trans hm)
    · exact hg (I.kept_inj h₁ h₂ h)

/-- A face off the pinch keeps its enumeration. -/
theorem keptCycle {g : Delta.toCombMap.Face} (hg₁ : g ≠ I.leftFace) (hg₂ : g ≠ I.rightFace) :
    (toCombMap Delta.toCombMap I.x I.y).IsFaceCycle (Delta.faceBoundary g).darts :=
  isFaceCycle_of_avoid Delta.toCombMap I.x I.y (Delta.faceBoundary g).isFaceCycle
    (by rw [FaceBoundary.faceOf_head]; exact hg₁) (by rw [FaceBoundary.faceOf_head]; exact hg₂)

theorem faceOf_out (F : (toCombMap Delta.toCombMap I.x I.y).Face) :
    (toCombMap Delta.toCombMap I.x I.y).faceOf F.out = F :=
  Quotient.out_eq F

theorem out_ne_left {F : (toCombMap Delta.toCombMap I.x I.y).Face} (hF : F ≠ I.merged) :
    Delta.toCombMap.faceOf F.out ≠ I.leftFace := fun h =>
  hF ((I.faceOf_out F).symm.trans ((I.cycles.faceOf_merged_iff _).mpr (Or.inl h)))

theorem out_ne_right {F : (toCombMap Delta.toCombMap I.x I.y).Face} (hF : F ≠ I.merged) :
    Delta.toCombMap.faceOf F.out ≠ I.rightFace := fun h =>
  hF ((I.faceOf_out F).symm.trans ((I.cycles.faceOf_merged_iff _).mpr (Or.inr h)))

/-- A kept face is represented by a dart of the old face. -/
theorem faceOf_out_kept {g : Delta.toCombMap.Face} (hg₁ : g ≠ I.leftFace)
    (hg₂ : g ≠ I.rightFace) : Delta.toCombMap.faceOf (I.kept g).out = g := by
  obtain ⟨d, rfl⟩ := Quotient.exists_rep g
  exact (faceOf_eq_iff_of_avoid Delta.toCombMap I.x I.y hg₁ hg₂ _).mp (I.faceOf_out _)

open scoped Classical in
/-- The face boundaries of the split: the merged enumeration at the merged face, the old walk at
every other face. -/
noncomputable def faceBoundary (F : (toCombMap Delta.toCombMap I.x I.y).Face) :
    FaceBoundary (toCombMap Delta.toCombMap I.x I.y) F :=
  if hF : F = I.merged then
    I.cycles.isFaceCycle_merged.toFaceBoundary.congr hF.symm
  else
    (I.keptCycle (I.out_ne_left hF) (I.out_ne_right hF)).toFaceBoundary.congr
      ((I.faceOf_congr (FaceBoundary.faceOf_head _)).trans (I.faceOf_out F))

/-- **The merged face reads the spliced enumeration.** -/
theorem faceBoundary_merged_darts :
    (I.faceBoundary I.merged).darts =
      Delta.toCombMap.alpha I.x :: I.cycles.ys ++ Delta.toCombMap.alpha I.y :: I.cycles.xs := by
  unfold faceBoundary
  rw [dif_pos rfl]
  rfl

/-- **A face off the pinch reads its old walk.** -/
theorem faceBoundary_kept_darts (g : Delta.toCombMap.Face) (hg₁ : g ≠ I.leftFace)
    (hg₂ : g ≠ I.rightFace) :
    (I.faceBoundary (I.kept g)).darts = (Delta.faceBoundary g).darts := by
  unfold faceBoundary
  rw [dif_neg (I.kept_ne_merged hg₁ hg₂)]
  change (Delta.faceBoundary (Delta.toCombMap.faceOf (I.kept g).out)).darts =
    (Delta.faceBoundary g).darts
  rw [I.faceOf_out_kept hg₁ hg₂]

/-- A relator record of the old diagram on the image of its face. -/
def cell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell (toCombMap Delta.toCombMap I.x I.y) (I.kept Delta.outerFace) W where
  face := I.kept C.face
  face_ne_outer := I.kept_ne_kept_outer C.face_ne_outer
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

theorem merged_faceWord_value :
    RelLetter.listVal ((I.faceBoundary I.merged).darts.map Delta.label) = 1 := by
  rw [I.faceBoundary_merged_darts]
  exact I.merged_listVal

/-- **The split disc diagram.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := toCombMap Delta.toCombMap I.x I.y
  planar := I.cycles.planar Delta.planar I.same_vertex
  label := Delta.label
  label_alpha := Delta.label_alpha
  outerFace := I.kept Delta.outerFace
  faceBoundary := I.faceBoundary
  relatorCells := Delta.relatorCells.map I.cell
  relatorCell_faces_nodup := by
    have hmap : (Delta.relatorCells.map I.cell).map RelatorCell.face =
        (Delta.relatorCells.map RelatorCell.face).map I.kept := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun _ _ => rfl
    rw [hmap]
    refine List.Nodup.map_on ?_ Delta.relatorCell_faces_nodup
    intro f hf f' _ hff'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hf
    exact I.kept_inj (I.left_not_cell C hC) (I.right_not_cell C hC) hff'
  relatorCell_word := by
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    change C.word = (I.faceBoundary (I.kept C.face)).darts.map Delta.label
    rw [I.faceBoundary_kept_darts C.face (I.left_not_cell C hC) (I.right_not_cell C hC)]
    exact Delta.relatorCell_word C hC
  inner_face := by
    intro F hF
    rcases I.face_cases F with rfl | ⟨g, hg₁, hg₂, rfl⟩
    · right
      exact I.merged_faceWord_value
    · have hgo : g ≠ Delta.outerFace := fun h => hF (by rw [h])
      rcases Delta.inner_face g hgo with ⟨C, hC, hface⟩ | hone
      · left
        refine ⟨I.cell C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        change I.kept C.face = I.kept g
        rw [hface]
      · right
        rw [I.faceBoundary_kept_darts g hg₁ hg₂]
        exact hone
  boundary_product := by
    have hvalues : (Delta.relatorCells.map I.cell).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      exact List.map_congr_left fun _ _ => rfl
    rw [hvalues, Delta.boundary_product]
    change RelLetter.listVal (RelWord.revInv ((Delta.faceBoundary Delta.outerFace).darts.map
        Delta.label)) =
      RelLetter.listVal (RelWord.revInv ((I.faceBoundary (I.kept Delta.outerFace)).darts.map
        Delta.label))
    rw [I.faceBoundary_kept_darts Delta.outerFace I.outer_ne_left I.outer_ne_right]

theorem diagram_toCombMap : I.diagram.toCombMap = toCombMap Delta.toCombMap I.x I.y := rfl

theorem diagram_outerFace : I.diagram.outerFace = I.kept Delta.outerFace := rfl

theorem diagram_faceOf (d : Delta.toCombMap.Dart) :
    I.diagram.toCombMap.faceOf d = I.kept (Delta.toCombMap.faceOf d) := rfl

/-- **The exterior boundary word is unchanged.** -/
theorem boundaryWord_eq : I.diagram.boundaryWord = Delta.boundaryWord := by
  change RelWord.revInv ((I.faceBoundary (I.kept Delta.outerFace)).darts.map Delta.label) =
    RelWord.revInv ((Delta.faceBoundary Delta.outerFace).darts.map Delta.label)
  rw [I.faceBoundary_kept_darts Delta.outerFace I.outer_ne_left I.outer_ne_right]

/-- **The ordered relator cells are the old ones**, on the images of their faces. -/
noncomputable def cellMap : Surgery.OrderedRCellMap Delta I.diagram I.kept where
  cell := I.cell
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

/-- The split is a G-region replacement. -/
noncomputable def replacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta :=
  ⟨I.diagram, I.boundaryWord_eq, I.cellMap.orderedTransport⟩

/-- **The split is O-equivalent to the old diagram.** -/
noncomputable def oEquivalent : OEquivalentDiscDiagram Delta I.diagram :=
  I.replacement.oEquivalent

/-- The split keeps the number of relator cells. -/
theorem rCellCount_eq : I.diagram.rCellCount = Delta.rCellCount :=
  I.cellMap.orderedTransport.rCellCount_eq

/-- **Reducedness survives the split.** -/
theorem reduced (hred : Delta.Reduced) : I.diagram.Reduced :=
  I.cellMap.orderedTransport.reduced hred

/-- Labels are unchanged, so legality is kept. -/
theorem label_isLetter (E : RelGenSet G Lambda) (h : ∀ d, E.IsLetter (Delta.label d))
    (d : I.diagram.toCombMap.Dart) : E.IsLetter (I.diagram.label d) :=
  h d

/-- The merged face is not the exterior. -/
theorem merged_ne_outer : I.merged ≠ I.diagram.outerFace :=
  fun h => I.kept_ne_merged I.outer_ne_left I.outer_ne_right h.symm

/-- No relator cell of the split sits on the merged face. -/
theorem merged_not_relatorFace : ∀ C ∈ I.diagram.relatorCells, C.face ≠ I.merged := by
  intro C hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  exact I.kept_ne_merged (I.left_not_cell C₀ hC₀) (I.right_not_cell C₀ hC₀)

/-- **The merged face is a G-face.** -/
theorem merged_value : RelLetter.listVal (I.diagram.faceWord I.merged) = 1 :=
  I.merged_faceWord_value

/-- A face off the pinch reads its old word. -/
theorem faceWord_kept (g : Delta.toCombMap.Face) (hg₁ : g ≠ I.leftFace) (hg₂ : g ≠ I.rightFace) :
    I.diagram.faceWord (I.kept g) = Delta.faceWord g :=
  congrArg (fun l => l.map Delta.label) (I.faceBoundary_kept_darts g hg₁ hg₂)

/-- **One face fewer.** -/
theorem faceCount_add_one : I.diagram.toCombMap.faceCount + 1 = Delta.toCombMap.faceCount :=
  I.cycles.faceCount_add_one

/-- One vertex more. -/
theorem vertexCount_eq : I.diagram.toCombMap.vertexCount = Delta.toCombMap.vertexCount + 1 :=
  PinchSplit.vertexCount_eq Delta.toCombMap I.x I.y I.same_vertex I.cycles.ne

end Input

end GroupApproximation.GGT.VanKampen.PinchSplit

#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.boundaryWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.cellMap
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.face_cases
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.kept_inj
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.faceBoundary_kept_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.faceBoundary_merged_darts
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.merged_value
#audit_axioms GroupApproximation.GGT.VanKampen.PinchSplit.Input.faceCount_add_one
