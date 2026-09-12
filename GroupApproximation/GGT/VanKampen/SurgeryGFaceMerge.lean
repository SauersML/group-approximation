import GroupApproximation.GGT.VanKampen.SurgeryGFaceMergeMap
import GroupApproximation.GGT.VanKampen.SurgeryCellMap
import GroupApproximation.GGT.VanKampen.SurgeryOrderedCells
import GroupApproximation.GGT.HullSCSmallCancellation
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# Merging two G-faces across a shared edge

The surgeries of Osin's Appendix (arXiv:math/0411039v3, §9: Lemma 9.4 Case 2) merge two
distinct G-faces of a disc diagram that share an edge.  A `GFaceMerge Δ` records such an
edge: a dart `dart` whose two sides `F₁ = faceOf dart` and `F₂ = faceOf (alpha dart)` are
distinct faces, neither the exterior nor a relator face.  Deleting the edge
(`EdgeDeletion.toCombMap`) merges `F₁` and `F₂` into one face and keeps every other face,
dart, label and relator cell.

The merged diagram `R.diagram` (Ξ below):

* its darts are the old darts off the deleted edge (`val`, `val_injective`, `val_ne`,
  `val_alpha`, `label_val`), with the total map `keep` back (`val_keep`, `keep_val`);
* its faces are the merged face `merged` and the kept faces `kept g` of the old faces
  `g ∉ {F₁, F₂}` (`face_cases`, `kept_inj`, `kept_ne_merged`, `kept_first`, `kept_second`);
  a dart lies on `kept g` exactly when its old face is `g` (`faceOf_val_kept`, `faceOf_keep`)
  and on `merged` exactly when its old face is `F₁` or `F₂` (`faceOf_val_merged`);
* a kept face reads its old traversal (`faceBoundary_kept_map_val`) and the merged face reads
  `xs ++ ys`, where `dart :: xs` and `alpha dart :: ys` are the two old faces enumerated from
  the edge (`merged_darts`);
* the merged face is a G-face (`merged_value`, `merged_ne_outer`,
  `merged_not_relatorFace`), and exactly one face disappears (`faceCount_add_one`);
* the exterior is the kept exterior (`outerFace_eq`), the boundary word is unchanged
  (`boundaryWord_eq`), and the relator cells are the old cells on their kept faces with the
  old words, conjugators and orientations, in the old order (`cellMap`).  So the merge is an
  `OrderedGRegionReplacement` (`replacement`), O-equivalent (`oEquivalent`), keeps the number
  of relator cells (`rCellCount_eq`) and reducedness (`reduced`), and keeps legal labels
  legal (`labelLegal`).
-/

namespace GroupApproximation.GGT.VanKampen.Surgery

open HullSC

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- **Two distinct G-faces sharing an edge**: the two sides of `dart` are different faces,
neither of them the exterior, and no relator cell sits on either. -/
structure GFaceMerge (Delta : DiscDiagram.{u, w, v} W) where
  /-- A dart of the shared edge. -/
  dart : Delta.toCombMap.Dart
  /-- The two sides of the edge lie on different faces. -/
  face_ne : Delta.toCombMap.faceOf dart ≠ Delta.toCombMap.faceOf (Delta.toCombMap.alpha dart)
  /-- The first side is not the exterior. -/
  first_ne_outer : Delta.toCombMap.faceOf dart ≠ Delta.outerFace
  /-- The second side is not the exterior. -/
  second_ne_outer : Delta.toCombMap.faceOf (Delta.toCombMap.alpha dart) ≠ Delta.outerFace
  /-- No relator cell sits on either side. -/
  cells_avoid : ∀ C ∈ Delta.relatorCells,
    C.face ≠ Delta.toCombMap.faceOf dart ∧
      C.face ≠ Delta.toCombMap.faceOf (Delta.toCombMap.alpha dart)

namespace GFaceMerge

open scoped Classical

variable {Delta : DiscDiagram.{u, w, v} W} (R : GFaceMerge Delta)

/-- The face of `dart`. -/
abbrev first : Delta.toCombMap.Face := Delta.toCombMap.faceOf R.dart

/-- The face of `alpha dart`. -/
abbrev second : Delta.toCombMap.Face := Delta.toCombMap.faceOf (Delta.toCombMap.alpha R.dart)

/-- The two old faces, enumerated from the shared edge. -/
noncomputable def cycles : EdgeDeletion.MergeCycles Delta.toCombMap R.dart :=
  EdgeDeletion.mergeCyclesOf Delta.toCombMap R.dart R.face_ne

theorem outerHead_off :
    (Delta.faceBoundary Delta.outerFace).darts.head (Delta.faceBoundary Delta.outerFace).nonempty ≠
        R.dart ∧
      (Delta.faceBoundary Delta.outerFace).darts.head (Delta.faceBoundary Delta.outerFace).nonempty ≠
        Delta.toCombMap.alpha R.dart := by
  have hface : Delta.toCombMap.faceOf ((Delta.faceBoundary Delta.outerFace).darts.head
      (Delta.faceBoundary Delta.outerFace).nonempty) = Delta.outerFace :=
    ((Delta.faceBoundary Delta.outerFace).mem_iff _).mp (List.head_mem _)
  refine ⟨fun h => R.first_ne_outer ?_, fun h => R.second_ne_outer ?_⟩
  · rw [← hface, h]
  · rw [← hface, h]

/-- A dart of the exterior survives the deletion. -/
noncomputable def outerDart : EdgeDeletion.Dart Delta.toCombMap R.dart :=
  EdgeDeletion.ofValue Delta.toCombMap R.dart
    ((Delta.faceBoundary Delta.outerFace).darts.head (Delta.faceBoundary Delta.outerFace).nonempty)
    R.outerHead_off.1 R.outerHead_off.2

theorem cycles_ne_nil : R.cycles.xs ++ R.cycles.ys ≠ [] :=
  R.cycles.append_ne_nil Delta.planar.1 R.outerDart

/-! ## The deleted map, its faces and traversals -/

/-- The map with the shared edge deleted. -/
noncomputable abbrev map : CombMap.{v} := EdgeDeletion.toCombMap Delta.toCombMap R.dart

/-- The merged face of the deleted map. -/
noncomputable def mergedFace : R.map.Face := R.cycles.mergedFace R.cycles_ne_nil

theorem outer_off : Delta.outerFace ≠ R.first ∧ Delta.outerFace ≠ R.second :=
  ⟨fun h => R.first_ne_outer h.symm, fun h => R.second_ne_outer h.symm⟩

/-- The face of the deleted map an old face goes to: its kept face when it is off both
sides, the merged face otherwise. -/
noncomputable def keptFace (g : Delta.toCombMap.Face) : R.map.Face :=
  if hg : g ≠ R.first ∧ g ≠ R.second then
    EdgeDeletion.keptFace Delta.toCombMap R.dart Delta.faceBoundary g hg
  else R.mergedFace

theorem keptFace_of_off {g : Delta.toCombMap.Face} (hg : g ≠ R.first ∧ g ≠ R.second) :
    R.keptFace g = EdgeDeletion.keptFace Delta.toCombMap R.dart Delta.faceBoundary g hg :=
  dif_pos hg

theorem keptFace_of_not_off {g : Delta.toCombMap.Face} (hg : ¬ (g ≠ R.first ∧ g ≠ R.second)) :
    R.keptFace g = R.mergedFace :=
  dif_neg hg

theorem keptFace_ne_mergedFace {g : Delta.toCombMap.Face} (hg : g ≠ R.first ∧ g ≠ R.second) :
    R.keptFace g ≠ R.mergedFace := by
  rw [R.keptFace_of_off hg]
  exact R.cycles.keptFace_ne_mergedFace Delta.faceBoundary R.cycles_ne_nil g hg

theorem keptFace_inj {g g' : Delta.toCombMap.Face} (hg : g ≠ R.first ∧ g ≠ R.second)
    (hg' : g' ≠ R.first ∧ g' ≠ R.second) (h : R.keptFace g = R.keptFace g') : g = g' := by
  rw [R.keptFace_of_off hg, R.keptFace_of_off hg'] at h
  exact EdgeDeletion.keptFace_inj h

theorem keptFace_ne_outer {g : Delta.toCombMap.Face} (hg : g ≠ Delta.outerFace) :
    R.keptFace g ≠ R.keptFace Delta.outerFace := by
  by_cases hoff : g ≠ R.first ∧ g ≠ R.second
  · exact fun h => hg (R.keptFace_inj hoff R.outer_off h)
  · rw [R.keptFace_of_not_off hoff]
    exact (R.keptFace_ne_mergedFace R.outer_off).symm

/-- The labels of the deleted map: the old labels. -/
def label (x : R.map.Dart) : RelLetter G Lambda :=
  Delta.label (EdgeDeletion.value Delta.toCombMap R.dart x)

theorem map_label (l : List R.map.Dart) :
    l.map R.label = (l.map (EdgeDeletion.value Delta.toCombMap R.dart)).map Delta.label := by
  induction l with
  | nil => rfl
  | cons x t ih => exact congrArg (List.cons (R.label x)) ih

/-- The traversals of the deleted map. -/
noncomputable def faceBoundary (F : R.map.Face) : FaceBoundary R.map F :=
  R.cycles.faceBoundary Delta.faceBoundary R.cycles_ne_nil F

/-- A kept face reads the old face word. -/
theorem keptFace_word {g : Delta.toCombMap.Face} (hg : g ≠ R.first ∧ g ≠ R.second) :
    (R.faceBoundary (R.keptFace g)).darts.map R.label = Delta.faceWord g := by
  rw [R.keptFace_of_off hg]
  exact (R.map_label _).trans (congrArg (List.map Delta.label)
    (R.cycles.faceBoundary_keptFace_map_value Delta.faceBoundary R.cycles_ne_nil g hg))

/-- The merged face reads `xs ++ ys`. -/
theorem mergedFace_word :
    (R.faceBoundary R.mergedFace).darts.map R.label =
      (R.cycles.xs ++ R.cycles.ys).map Delta.label :=
  (R.map_label _).trans (congrArg (List.map Delta.label)
    (R.cycles.faceBoundary_mergedFace_map_value Delta.faceBoundary R.cycles_ne_nil))

/-! ## The merged face is a G-face -/

theorem word_rotate_value_one (l : List (RelLetter G Lambda)) {k : ℕ} (hk : k ≤ l.length)
    (h : RelLetter.listVal l = 1) : RelLetter.listVal (l.rotate k) = 1 := by
  rw [RelWord.listVal_rotate l hk, h]
  simp

theorem gFace_value {g : Delta.toCombMap.Face} (hg : g ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ g) :
    RelLetter.listVal (Delta.faceWord g) = 1 := by
  rcases Delta.inner_face g hg with ⟨C, hC, hface⟩ | hval
  · exact absurd hface (hcells C hC)
  · exact hval

theorem cycle_value_one {g : Delta.toCombMap.Face} (hg : g ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, C.face ≠ g) {d : Delta.toCombMap.Dart}
    {rest : List Delta.toCombMap.Dart} (hcyc : Delta.toCombMap.IsFaceCycle (d :: rest))
    (hd : Delta.toCombMap.faceOf d = g) :
    RelLetter.listVal ((d :: rest).map Delta.label) = 1 := by
  have hB := (Delta.faceBoundary g).isFaceCycle
  have hface : Delta.toCombMap.faceOf ((Delta.faceBoundary g).darts.head hB.ne_nil) =
      Delta.toCombMap.faceOf ((d :: rest).head hcyc.ne_nil) :=
    (((Delta.faceBoundary g).mem_iff _).mp (List.head_mem _)).trans hd.symm
  obtain ⟨k, hk, hrot⟩ := hB.exists_rotate_eq hcyc hface
  rw [← hrot, List.map_rotate]
  exact word_rotate_value_one _ (by rw [List.length_map]; exact hk) (gFace_value hg hcells)

theorem first_value : RelLetter.listVal ((R.dart :: R.cycles.xs).map Delta.label) = 1 :=
  cycle_value_one R.first_ne_outer (fun C hC => (R.cells_avoid C hC).1) R.cycles.cycO rfl

theorem second_value :
    RelLetter.listVal ((Delta.toCombMap.alpha R.dart :: R.cycles.ys).map Delta.label) = 1 :=
  cycle_value_one R.second_ne_outer (fun C hC => (R.cells_avoid C hC).2) R.cycles.cycG rfl

/-- **The merged face reads a trivial element.** -/
theorem mergedFace_value :
    RelLetter.listVal ((R.faceBoundary R.mergedFace).darts.map R.label) = 1 := by
  rw [R.mergedFace_word, List.map_append, RelWord.listVal_append]
  have h1 := R.first_value
  have h2 := R.second_value
  rw [List.map_cons, RelWord.listVal_cons] at h1 h2
  rw [Delta.label_alpha, RelWord.val_inv] at h2
  rw [eq_inv_of_mul_eq_one_right h1, eq_inv_of_mul_eq_one_right h2]
  simp

/-! ## The merged diagram -/

/-- A relator record of the old diagram, on its kept face, with its word, conjugator and
orientation unchanged. -/
noncomputable def cell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell R.map (R.keptFace Delta.outerFace) W where
  face := R.keptFace C.face
  face_ne_outer := R.keptFace_ne_outer C.face_ne_outer
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

theorem cells_value_map :
    (Delta.relatorCells.map R.cell).map RelatorCell.value =
      Delta.relatorCells.map RelatorCell.value := by
  rw [List.map_map]
  exact List.map_congr_left fun _ _ => rfl

/-- **The merged diagram.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := R.map
  planar := EdgeDeletion.planar_of_neFace Delta.toCombMap R.dart Delta.planar R.outerDart
    R.face_ne
  label := R.label
  label_alpha := fun x =>
    (congrArg Delta.label (EdgeDeletion.alpha_val Delta.toCombMap R.dart x)).trans
      (Delta.label_alpha _)
  outerFace := R.keptFace Delta.outerFace
  faceBoundary := R.faceBoundary
  relatorCells := Delta.relatorCells.map R.cell
  relatorCell_faces_nodup := by
    have hmap : (Delta.relatorCells.map R.cell).map RelatorCell.face =
        (Delta.relatorCells.map RelatorCell.face).map R.keptFace := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun _ _ => rfl
    rw [hmap]
    refine List.Nodup.map_on ?_ Delta.relatorCell_faces_nodup
    intro x hx y hy hxy
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hx
    obtain ⟨C', hC', rfl⟩ := List.mem_map.mp hy
    exact R.keptFace_inj (R.cells_avoid C hC) (R.cells_avoid C' hC') hxy
  relatorCell_word := by
    intro C' hC'
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    change C.word = (R.faceBoundary (R.keptFace C.face)).darts.map R.label
    rw [R.keptFace_word (R.cells_avoid C hC)]
    exact Delta.relatorCell_word C hC
  inner_face := by
    intro F hF
    rcases R.cycles.face_cases Delta.faceBoundary R.cycles_ne_nil F with hm | ⟨g, hg, rfl⟩
    · right
      rw [hm]
      exact R.mergedFace_value
    · have hgo : g ≠ Delta.outerFace := fun h =>
        hF ((EdgeDeletion.keptFace_congr Delta.faceBoundary hg R.outer_off h).trans
          (R.keptFace_of_off R.outer_off).symm)
      rcases Delta.inner_face g hgo with ⟨C, hC, hface⟩ | hval
      · left
        refine ⟨R.cell C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        show R.keptFace C.face = EdgeDeletion.keptFace Delta.toCombMap R.dart Delta.faceBoundary g hg
        rw [R.keptFace_of_off (R.cells_avoid C hC)]
        exact EdgeDeletion.keptFace_congr Delta.faceBoundary _ hg hface
      · right
        have hw := R.keptFace_word hg
        rw [R.keptFace_of_off hg] at hw
        exact (congrArg RelLetter.listVal hw).trans hval
  boundary_product :=
    (congrArg List.prod R.cells_value_map).trans
      (Delta.boundary_product.trans
        (congrArg (fun l => RelLetter.listVal (RelWord.revInv l))
          (R.keptFace_word R.outer_off).symm))

/-! ## Darts -/

/-- The old dart under a dart of the merge. -/
def val (x : R.diagram.toCombMap.Dart) : Delta.toCombMap.Dart :=
  EdgeDeletion.value Delta.toCombMap R.dart x

theorem val_injective : Function.Injective R.val :=
  EdgeDeletion.value_injective Delta.toCombMap R.dart

theorem val_ne (x : R.diagram.toCombMap.Dart) :
    R.val x ≠ R.dart ∧ R.val x ≠ Delta.toCombMap.alpha R.dart :=
  ⟨EdgeDeletion.value_ne Delta.toCombMap R.dart x,
    EdgeDeletion.value_ne_reverse Delta.toCombMap R.dart x⟩

theorem val_alpha (x : R.diagram.toCombMap.Dart) :
    R.val (R.diagram.toCombMap.alpha x) = Delta.toCombMap.alpha (R.val x) :=
  EdgeDeletion.alpha_val Delta.toCombMap R.dart x

theorem label_val (x : R.diagram.toCombMap.Dart) :
    R.diagram.label x = Delta.label (R.val x) :=
  rfl

/-- The total dart map: an old dart off the deleted edge to itself, the two deleted darts to
a dart of the exterior. -/
noncomputable def keep (d : Delta.toCombMap.Dart) : R.diagram.toCombMap.Dart :=
  if h : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart then
    EdgeDeletion.ofValue Delta.toCombMap R.dart d h.1 h.2
  else R.outerDart

theorem keep_of_off {d : Delta.toCombMap.Dart}
    (h : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    R.keep d = EdgeDeletion.ofValue Delta.toCombMap R.dart d h.1 h.2 :=
  dif_pos h

theorem val_keep {d : Delta.toCombMap.Dart} (h : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) :
    R.val (R.keep d) = d := by
  rw [R.keep_of_off h]
  rfl

theorem keep_val (x : R.diagram.toCombMap.Dart) : R.keep (R.val x) = x :=
  R.val_injective (R.val_keep (R.val_ne x))

/-! ## Faces -/

/-- The face of the merge an old face goes to: its kept face off both sides, the merged face
on them. -/
noncomputable def kept (g : Delta.toCombMap.Face) : R.diagram.toCombMap.Face := R.keptFace g

/-- **The merged face.** -/
noncomputable def merged : R.diagram.toCombMap.Face := R.mergedFace

theorem kept_first : R.kept R.first = R.merged :=
  R.keptFace_of_not_off fun h => h.1 rfl

theorem kept_second : R.kept R.second = R.merged :=
  R.keptFace_of_not_off fun h => h.2 rfl

theorem kept_ne_merged {g : Delta.toCombMap.Face} (hg : g ≠ R.first ∧ g ≠ R.second) :
    R.kept g ≠ R.merged :=
  R.keptFace_ne_mergedFace hg

theorem kept_inj {g g' : Delta.toCombMap.Face} (hg : g ≠ R.first ∧ g ≠ R.second)
    (hg' : g' ≠ R.first ∧ g' ≠ R.second) (h : R.kept g = R.kept g') : g = g' :=
  R.keptFace_inj hg hg' h

/-- **Every face of the merge is the merged face or a kept face.** -/
theorem face_cases (F : R.diagram.toCombMap.Face) :
    F = R.merged ∨ ∃ g : Delta.toCombMap.Face, g ≠ R.first ∧ g ≠ R.second ∧ F = R.kept g := by
  rcases R.cycles.face_cases Delta.faceBoundary R.cycles_ne_nil F with hm | ⟨g, hg, hF⟩
  · exact Or.inl hm
  · exact Or.inr ⟨g, hg.1, hg.2, hF.trans (R.keptFace_of_off hg).symm⟩

theorem outerFace_eq : R.diagram.outerFace = R.kept Delta.outerFace :=
  rfl

/-- A dart whose old face is off both sides lies on the kept face of its old face. -/
theorem faceOf_val_kept (x : R.diagram.toCombMap.Dart)
    (hg : Delta.toCombMap.faceOf (R.val x) ≠ R.first ∧
      Delta.toCombMap.faceOf (R.val x) ≠ R.second) :
    R.diagram.toCombMap.faceOf x = R.kept (Delta.toCombMap.faceOf (R.val x)) := by
  show R.map.faceOf x = R.keptFace (Delta.toCombMap.faceOf (R.val x))
  rw [R.keptFace_of_off hg]
  exact (EdgeDeletion.faceOf_eq_keptFace_iff Delta.faceBoundary _ hg x).mpr rfl

/-- A dart whose old face is one of the two sides lies on the merged face. -/
theorem faceOf_val_merged (x : R.diagram.toCombMap.Dart)
    (h : Delta.toCombMap.faceOf (R.val x) = R.first ∨
      Delta.toCombMap.faceOf (R.val x) = R.second) :
    R.diagram.toCombMap.faceOf x = R.merged :=
  (R.cycles.faceOf_eq_mergedFace_iff R.cycles_ne_nil x).mpr h

/-- A dart on a face off both sides lies, through `keep`, on the kept face. -/
theorem faceOf_keep {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d ≠ R.first ∧ Delta.toCombMap.faceOf d ≠ R.second) :
    R.diagram.toCombMap.faceOf (R.keep d) = R.kept (Delta.toCombMap.faceOf d) := by
  have havoid := EdgeDeletion.avoid_of_off hd rfl
  have hval := R.val_keep ⟨havoid.1, havoid.2.1⟩
  have h := R.faceOf_val_kept (R.keep d) (by rw [hval]; exact hd)
  rwa [hval] at h

/-- A surviving dart on one of the two sides lies, through `keep`, on the merged face. -/
theorem faceOf_keep_merged {d : Delta.toCombMap.Dart}
    (hd : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart)
    (h : Delta.toCombMap.faceOf d = R.first ∨ Delta.toCombMap.faceOf d = R.second) :
    R.diagram.toCombMap.faceOf (R.keep d) = R.merged := by
  apply R.faceOf_val_merged
  rw [R.val_keep hd]
  exact h

/-! ## Walks -/

/-- A kept face reads its old traversal. -/
theorem faceBoundary_kept_map_val (g : Delta.toCombMap.Face)
    (hg : g ≠ R.first ∧ g ≠ R.second) :
    (R.diagram.faceBoundary (R.kept g)).darts.map R.val = (Delta.faceBoundary g).darts := by
  have hk : R.kept g = EdgeDeletion.keptFace Delta.toCombMap R.dart Delta.faceBoundary g hg :=
    R.keptFace_of_off hg
  rw [hk]
  exact R.cycles.faceBoundary_keptFace_map_value Delta.faceBoundary R.cycles_ne_nil g hg

/-- **The merged face reads `xs ++ ys`**, where `dart :: xs` and `alpha dart :: ys` are the
two old faces enumerated from the shared edge. -/
theorem merged_darts : ∃ xs ys : List Delta.toCombMap.Dart,
    Delta.toCombMap.IsFaceCycle (R.dart :: xs) ∧
      Delta.toCombMap.IsFaceCycle (Delta.toCombMap.alpha R.dart :: ys) ∧
        (R.diagram.faceBoundary R.merged).darts.map R.val = xs ++ ys :=
  ⟨R.cycles.xs, R.cycles.ys, R.cycles.cycO, R.cycles.cycG,
    R.cycles.faceBoundary_mergedFace_map_value Delta.faceBoundary R.cycles_ne_nil⟩

/-! ## The merged face -/

/-- **The merged face is a G-face.** -/
theorem merged_value : RelLetter.listVal (R.diagram.faceWord R.merged) = 1 :=
  R.mergedFace_value

theorem merged_ne_outer : R.merged ≠ R.diagram.outerFace :=
  (R.keptFace_ne_mergedFace R.outer_off).symm

theorem merged_not_relatorFace : ∀ C ∈ R.diagram.relatorCells, C.face ≠ R.merged := by
  intro C hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  exact R.keptFace_ne_mergedFace (R.cells_avoid C₀ hC₀)

/-- **Exactly one face disappears.** -/
theorem faceCount_add_one :
    R.diagram.toCombMap.faceCount + 1 = Delta.toCombMap.faceCount :=
  R.cycles.faceCount_add_one Delta.planar.1 R.outerDart

/-! ## The diagram-level records -/

/-- The exterior boundary word is unchanged. -/
theorem boundaryWord_eq : R.diagram.boundaryWord = Delta.boundaryWord :=
  congrArg RelWord.revInv (R.keptFace_word R.outer_off)

/-- The ordered relator cells are the old ones, on their kept faces. -/
noncomputable def cellMap : OrderedRCellMap Delta R.diagram R.kept where
  cell := R.cell
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

/-- **The merge is a G-region replacement.** -/
noncomputable def replacement : OrderedGRegionReplacement.{u, w, v, v} Delta :=
  ⟨R.diagram, R.boundaryWord_eq, R.cellMap.orderedTransport⟩

/-- The merge is O-equivalent to the old diagram. -/
noncomputable def oEquivalent : OEquivalentDiscDiagram Delta R.diagram :=
  R.replacement.oEquivalent

theorem rCellCount_eq : R.diagram.rCellCount = Delta.rCellCount :=
  R.cellMap.orderedTransport.rCellCount_eq

/-- Reducedness survives the merge. -/
theorem reduced (hred : Delta.Reduced) : R.diagram.Reduced :=
  R.cellMap.orderedTransport.reduced hred

/-- Legal labels stay legal: every label of the merge is an old label. -/
theorem labelLegal (E : RelGenSet G Lambda) (h : ∀ d, E.IsLetter (Delta.label d))
    (x : R.diagram.toCombMap.Dart) : E.IsLetter (R.diagram.label x) :=
  h (R.val x)

end GFaceMerge

end GroupApproximation.GGT.VanKampen.Surgery

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.face_cases
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.faceOf_keep
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.faceBoundary_kept_map_val
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.merged_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.merged_value
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.merged_not_relatorFace
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.faceCount_add_one
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.boundaryWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.cellMap
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.GFaceMerge.labelLegal
