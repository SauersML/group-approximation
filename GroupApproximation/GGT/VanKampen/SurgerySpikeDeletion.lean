import GroupApproximation.GGT.VanKampen.SurgeryGFaceMerge
import GroupApproximation.GGT.VanKampen.SurgerySpikeDeletionMap
import GroupApproximation.Meta.AxiomGuard

/-!
# Deleting a spike from a G-face

Case 2 in the proof of Osin's Lemma 9.4 (arXiv:math/0411039v3, §9), measured by dart count,
removes a dangling path from a G-face one edge at a time, starting at its free end.  A
`SpikeDeletion Δ` records one such edge: a dart `dart` fixed by the vertex rotation (the tip of
a spike), on a face `F = faceOf dart` that is neither the exterior nor a relator face.  Both
sides of the edge lie on `F`, which reads `alpha dart :: dart :: rest` from the edge
(`EdgeDeletion.SpikeCycle`).  Deleting the edge (`EdgeDeletion.toCombMap`) shrinks `F` to the
face reading `rest` and keeps every other face, dart, label and relator cell.

The deleted diagram `R.diagram` (Ξ below):

* its darts are the old darts off the deleted edge (`val`, `val_injective`, `val_ne`,
  `val_alpha`, `label_val`), with the total map `keep` back (`val_keep`, `keep_val`);
* its faces are the shrunk face `shrunk` and the kept faces `kept g` of the old faces `g ≠ F`
  (`face_cases`, `kept_inj`, `kept_ne_shrunk`, `kept_face`); a dart lies on `kept g` exactly
  when its old face is `g` (`faceOf_val_kept`, `faceOf_keep`) and on `shrunk` exactly when its
  old face is `F` (`faceOf_val_shrunk`);
* a kept face reads its old traversal (`faceBoundary_kept_map_val`) and the shrunk face reads
  `rest` (`shrunk_darts`);
* the shrunk face is a G-face (`shrunk_value`, `shrunk_ne_outer`, `shrunk_not_relatorFace`),
  no face disappears (`faceCount_eq`), and two darts disappear (`dartCount_add_two`);
* the exterior is the kept exterior (`outerFace_eq`), the boundary word is unchanged
  (`boundaryWord_eq`), and the relator cells are the old cells on their kept faces with the
  old words, conjugators and orientations, in the old order (`cellMap`).  So the deletion is
  an `OrderedGRegionReplacement` (`replacement`), O-equivalent (`oEquivalent`), keeps the
  number of relator cells (`rCellCount_eq`) and reducedness (`reduced`), and keeps legal
  labels legal (`labelLegal`).
-/

namespace GroupApproximation.GGT.VanKampen.Surgery

open HullSC

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- **The tip of a spike in a G-face**: a dart fixed by the vertex rotation, on a face that is
neither the exterior nor a relator face. -/
structure SpikeDeletion (Delta : DiscDiagram.{u, w, v} W) where
  /-- The tip of the spike. -/
  dart : Delta.toCombMap.Dart
  /-- The tip is the only dart at its vertex. -/
  sigma_eq : Delta.toCombMap.sigma dart = dart
  /-- The face of the spike is not the exterior. -/
  face_ne_outer : Delta.toCombMap.faceOf dart ≠ Delta.outerFace
  /-- No relator cell sits on the face of the spike. -/
  cells_avoid : ∀ C ∈ Delta.relatorCells, C.face ≠ Delta.toCombMap.faceOf dart

namespace SpikeDeletion

open scoped Classical

variable {Delta : DiscDiagram.{u, w, v} W} (R : SpikeDeletion Delta)

/-- The face of the spike. -/
abbrev face : Delta.toCombMap.Face := Delta.toCombMap.faceOf R.dart

/-- The face of the spike, enumerated from the edge. -/
noncomputable def cycle : EdgeDeletion.SpikeCycle Delta.toCombMap R.dart :=
  EdgeDeletion.spikeCycleOf Delta.toCombMap R.dart R.sigma_eq

/-- Both sides of the edge lie on the face of the spike. -/
theorem faceOf_alpha : Delta.toCombMap.faceOf (Delta.toCombMap.alpha R.dart) = R.face :=
  R.cycle.faceOf_alpha

/-- A face other than the face of the spike is off both sides of the edge. -/
theorem off {g : Delta.toCombMap.Face} (hg : g ≠ R.face) :
    g ≠ Delta.toCombMap.faceOf R.dart ∧
      g ≠ Delta.toCombMap.faceOf (Delta.toCombMap.alpha R.dart) :=
  ⟨hg, fun h => hg (h.trans R.faceOf_alpha)⟩

theorem outer_ne : Delta.outerFace ≠ R.face := fun h => R.face_ne_outer h.symm

theorem outerHead_off :
    (Delta.faceBoundary Delta.outerFace).darts.head
        (Delta.faceBoundary Delta.outerFace).nonempty ≠ R.dart ∧
      (Delta.faceBoundary Delta.outerFace).darts.head
          (Delta.faceBoundary Delta.outerFace).nonempty ≠ Delta.toCombMap.alpha R.dart := by
  have h := EdgeDeletion.avoid_of_off (R.off R.outer_ne)
    (((Delta.faceBoundary Delta.outerFace).mem_iff _).mp
      (List.head_mem (Delta.faceBoundary Delta.outerFace).nonempty))
  exact ⟨h.1, h.2.1⟩

/-- A dart of the exterior survives the deletion. -/
noncomputable def outerDart : EdgeDeletion.Dart Delta.toCombMap R.dart :=
  EdgeDeletion.ofValue Delta.toCombMap R.dart
    ((Delta.faceBoundary Delta.outerFace).darts.head (Delta.faceBoundary Delta.outerFace).nonempty)
    R.outerHead_off.1 R.outerHead_off.2

theorem rest_ne_nil : R.cycle.rest ≠ [] :=
  R.cycle.rest_ne_nil Delta.planar.1 R.outerDart

/-! ## The deleted map, its faces and traversals -/

/-- The map with the edge of the spike deleted. -/
noncomputable abbrev map : CombMap.{v} := EdgeDeletion.toCombMap Delta.toCombMap R.dart

/-- The shrunk face of the deleted map. -/
noncomputable def shrunkFace : R.map.Face := R.cycle.shrunkFace R.rest_ne_nil

/-- The face of the deleted map an old face goes to: its kept face off the face of the spike,
the shrunk face on it. -/
noncomputable def keptFace (g : Delta.toCombMap.Face) : R.map.Face :=
  if hg : g ≠ R.face then
    EdgeDeletion.keptFace Delta.toCombMap R.dart Delta.faceBoundary g (R.off hg)
  else R.shrunkFace

theorem keptFace_of_off {g : Delta.toCombMap.Face} (hg : g ≠ R.face) :
    R.keptFace g = EdgeDeletion.keptFace Delta.toCombMap R.dart Delta.faceBoundary g (R.off hg) :=
  dif_pos hg

theorem keptFace_of_not_off {g : Delta.toCombMap.Face} (hg : ¬ g ≠ R.face) :
    R.keptFace g = R.shrunkFace :=
  dif_neg hg

theorem keptFace_ne_shrunkFace {g : Delta.toCombMap.Face} (hg : g ≠ R.face) :
    R.keptFace g ≠ R.shrunkFace := by
  rw [R.keptFace_of_off hg]
  exact R.cycle.keptFace_ne_shrunkFace Delta.faceBoundary R.rest_ne_nil g (R.off hg)

theorem keptFace_inj {g g' : Delta.toCombMap.Face} (hg : g ≠ R.face) (hg' : g' ≠ R.face)
    (h : R.keptFace g = R.keptFace g') : g = g' := by
  rw [R.keptFace_of_off hg, R.keptFace_of_off hg'] at h
  exact EdgeDeletion.keptFace_inj h

theorem keptFace_ne_outer {g : Delta.toCombMap.Face} (hg : g ≠ Delta.outerFace) :
    R.keptFace g ≠ R.keptFace Delta.outerFace := by
  by_cases hoff : g ≠ R.face
  · exact fun h => hg (R.keptFace_inj hoff R.outer_ne h)
  · rw [R.keptFace_of_not_off hoff]
    exact (R.keptFace_ne_shrunkFace R.outer_ne).symm

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
  R.cycle.faceBoundary Delta.faceBoundary R.rest_ne_nil F

/-- A kept face reads the old face word. -/
theorem keptFace_word {g : Delta.toCombMap.Face} (hg : g ≠ R.face) :
    (R.faceBoundary (R.keptFace g)).darts.map R.label = Delta.faceWord g := by
  rw [R.keptFace_of_off hg]
  exact (R.map_label _).trans (congrArg (List.map Delta.label)
    (R.cycle.faceBoundary_keptFace_map_value Delta.faceBoundary R.rest_ne_nil g (R.off hg)))

/-- The shrunk face reads `rest`. -/
theorem shrunkFace_word :
    (R.faceBoundary R.shrunkFace).darts.map R.label = R.cycle.rest.map Delta.label :=
  (R.map_label _).trans (congrArg (List.map Delta.label)
    (R.cycle.faceBoundary_shrunkFace_map_value Delta.faceBoundary R.rest_ne_nil))

/-! ## The shrunk face is a G-face -/

theorem face_value :
    RelLetter.listVal
        ((Delta.toCombMap.alpha R.dart :: R.dart :: R.cycle.rest).map Delta.label) = 1 :=
  GFaceMerge.cycle_value_one R.face_ne_outer R.cells_avoid R.cycle.cyc R.faceOf_alpha

/-- **The shrunk face reads a trivial element**: the old face word is `x⁻¹ x` followed by
the word of `rest`. -/
theorem shrunkFace_value :
    RelLetter.listVal ((R.faceBoundary R.shrunkFace).darts.map R.label) = 1 := by
  have h := R.face_value
  rw [List.map_cons, RelWord.listVal_cons, List.map_cons, RelWord.listVal_cons,
    Delta.label_alpha, RelWord.val_inv, inv_mul_cancel_left] at h
  rw [R.shrunkFace_word]
  exact h

/-! ## The deleted diagram -/

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

/-- **The deleted diagram.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := R.map
  planar := EdgeDeletion.planar_of_sigma_fixed Delta.toCombMap R.dart Delta.planar R.sigma_eq
    R.outerDart
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
    rcases R.cycle.face_cases Delta.faceBoundary R.rest_ne_nil F with hm | ⟨g, hg, rfl⟩
    · right
      rw [hm]
      exact R.shrunkFace_value
    · have hgo : g ≠ Delta.outerFace := fun h =>
        hF ((EdgeDeletion.keptFace_congr Delta.faceBoundary hg (R.off R.outer_ne) h).trans
          (R.keptFace_of_off R.outer_ne).symm)
      rcases Delta.inner_face g hgo with ⟨C, hC, hface⟩ | hval
      · left
        refine ⟨R.cell C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
        show R.keptFace C.face =
          EdgeDeletion.keptFace Delta.toCombMap R.dart Delta.faceBoundary g hg
        rw [R.keptFace_of_off (R.cells_avoid C hC)]
        exact EdgeDeletion.keptFace_congr Delta.faceBoundary _ hg hface
      · right
        have hw := R.keptFace_word hg.1
        rw [R.keptFace_of_off hg.1] at hw
        exact (congrArg RelLetter.listVal hw).trans hval
  boundary_product :=
    (congrArg List.prod R.cells_value_map).trans
      (Delta.boundary_product.trans
        (congrArg (fun l => RelLetter.listVal (RelWord.revInv l))
          (R.keptFace_word R.outer_ne).symm))

/-! ## Darts -/

/-- The old dart under a dart of the deletion. -/
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

theorem val_keep {d : Delta.toCombMap.Dart}
    (h : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart) : R.val (R.keep d) = d := by
  rw [R.keep_of_off h]
  rfl

theorem keep_val (x : R.diagram.toCombMap.Dart) : R.keep (R.val x) = x :=
  R.val_injective (R.val_keep (R.val_ne x))

/-! ## Faces -/

/-- The face of the deletion an old face goes to: its kept face off the face of the spike, the
shrunk face on it. -/
noncomputable def kept (g : Delta.toCombMap.Face) : R.diagram.toCombMap.Face := R.keptFace g

/-- **The shrunk face.** -/
noncomputable def shrunk : R.diagram.toCombMap.Face := R.shrunkFace

theorem kept_face : R.kept R.face = R.shrunk :=
  R.keptFace_of_not_off fun h => h rfl

theorem kept_ne_shrunk {g : Delta.toCombMap.Face} (hg : g ≠ R.face) : R.kept g ≠ R.shrunk :=
  R.keptFace_ne_shrunkFace hg

theorem kept_inj {g g' : Delta.toCombMap.Face} (hg : g ≠ R.face) (hg' : g' ≠ R.face)
    (h : R.kept g = R.kept g') : g = g' :=
  R.keptFace_inj hg hg' h

/-- **Every face of the deletion is the shrunk face or a kept face.** -/
theorem face_cases (F : R.diagram.toCombMap.Face) :
    F = R.shrunk ∨ ∃ g : Delta.toCombMap.Face, g ≠ R.face ∧ F = R.kept g := by
  rcases R.cycle.face_cases Delta.faceBoundary R.rest_ne_nil F with hm | ⟨g, hg, hF⟩
  · exact Or.inl hm
  · exact Or.inr ⟨g, hg.1, hF.trans (R.keptFace_of_off hg.1).symm⟩

theorem outerFace_eq : R.diagram.outerFace = R.kept Delta.outerFace :=
  rfl

/-- A dart whose old face is not the face of the spike lies on the kept face of its old
face. -/
theorem faceOf_val_kept (x : R.diagram.toCombMap.Dart)
    (hg : Delta.toCombMap.faceOf (R.val x) ≠ R.face) :
    R.diagram.toCombMap.faceOf x = R.kept (Delta.toCombMap.faceOf (R.val x)) := by
  show R.map.faceOf x = R.keptFace (Delta.toCombMap.faceOf (R.val x))
  rw [R.keptFace_of_off hg]
  exact (EdgeDeletion.faceOf_eq_keptFace_iff Delta.faceBoundary _ (R.off hg) x).mpr rfl

/-- A dart whose old face is the face of the spike lies on the shrunk face. -/
theorem faceOf_val_shrunk (x : R.diagram.toCombMap.Dart)
    (h : Delta.toCombMap.faceOf (R.val x) = R.face) :
    R.diagram.toCombMap.faceOf x = R.shrunk :=
  (R.cycle.faceOf_eq_shrunkFace_iff R.rest_ne_nil x).mpr h

/-- A dart on a face other than the face of the spike lies, through `keep`, on the kept
face. -/
theorem faceOf_keep {d : Delta.toCombMap.Dart} (hd : Delta.toCombMap.faceOf d ≠ R.face) :
    R.diagram.toCombMap.faceOf (R.keep d) = R.kept (Delta.toCombMap.faceOf d) := by
  have havoid := EdgeDeletion.avoid_of_off (R.off hd) rfl
  have hval := R.val_keep ⟨havoid.1, havoid.2.1⟩
  have h := R.faceOf_val_kept (R.keep d) (by rw [hval]; exact hd)
  rwa [hval] at h

/-- A surviving dart on the face of the spike lies, through `keep`, on the shrunk face. -/
theorem faceOf_keep_shrunk {d : Delta.toCombMap.Dart}
    (hd : d ≠ R.dart ∧ d ≠ Delta.toCombMap.alpha R.dart)
    (h : Delta.toCombMap.faceOf d = R.face) :
    R.diagram.toCombMap.faceOf (R.keep d) = R.shrunk := by
  apply R.faceOf_val_shrunk
  rw [R.val_keep hd]
  exact h

/-! ## Walks -/

/-- A kept face reads its old traversal. -/
theorem faceBoundary_kept_map_val (g : Delta.toCombMap.Face) (hg : g ≠ R.face) :
    (R.diagram.faceBoundary (R.kept g)).darts.map R.val = (Delta.faceBoundary g).darts := by
  have hk : R.kept g =
      EdgeDeletion.keptFace Delta.toCombMap R.dart Delta.faceBoundary g (R.off hg) :=
    R.keptFace_of_off hg
  rw [hk]
  exact R.cycle.faceBoundary_keptFace_map_value Delta.faceBoundary R.rest_ne_nil g (R.off hg)

/-- **The shrunk face reads `rest`**, where `alpha dart :: dart :: rest` is the old face
enumerated from the edge. -/
theorem shrunk_darts : ∃ rest : List Delta.toCombMap.Dart,
    Delta.toCombMap.IsFaceCycle (Delta.toCombMap.alpha R.dart :: R.dart :: rest) ∧
      (R.diagram.faceBoundary R.shrunk).darts.map R.val = rest :=
  ⟨R.cycle.rest, R.cycle.cyc,
    R.cycle.faceBoundary_shrunkFace_map_value Delta.faceBoundary R.rest_ne_nil⟩

/-! ## The shrunk face -/

/-- **The shrunk face is a G-face.** -/
theorem shrunk_value : RelLetter.listVal (R.diagram.faceWord R.shrunk) = 1 :=
  R.shrunkFace_value

theorem shrunk_ne_outer : R.shrunk ≠ R.diagram.outerFace :=
  (R.keptFace_ne_shrunkFace R.outer_ne).symm

theorem shrunk_not_relatorFace : ∀ C ∈ R.diagram.relatorCells, C.face ≠ R.shrunk := by
  intro C hC
  obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
  exact R.keptFace_ne_shrunkFace (R.cells_avoid C₀ hC₀)

/-- **No face disappears.** -/
theorem faceCount_eq : R.diagram.toCombMap.faceCount = Delta.toCombMap.faceCount :=
  R.cycle.faceCount_eq Delta.planar R.outerDart

/-- **Two darts disappear.** -/
theorem dartCount_add_two : R.diagram.toCombMap.dartCount + 2 = Delta.toCombMap.dartCount :=
  EdgeDeletion.dartCount_add_two Delta.toCombMap R.dart

/-! ## The diagram-level records -/

/-- The exterior boundary word is unchanged. -/
theorem boundaryWord_eq : R.diagram.boundaryWord = Delta.boundaryWord :=
  congrArg RelWord.revInv (R.keptFace_word R.outer_ne)

/-- The ordered relator cells are the old ones, on their kept faces. -/
noncomputable def cellMap : OrderedRCellMap Delta R.diagram R.kept where
  cell := R.cell
  face_eq _ := rfl
  word_eq _ := rfl
  conjugator_eq _ := rfl
  reversed_eq _ := rfl
  list_eq := rfl

/-- **The deletion is a G-region replacement.** -/
noncomputable def replacement : OrderedGRegionReplacement.{u, w, v, v} Delta :=
  ⟨R.diagram, R.boundaryWord_eq, R.cellMap.orderedTransport⟩

/-- The deletion is O-equivalent to the old diagram. -/
noncomputable def oEquivalent : OEquivalentDiscDiagram Delta R.diagram :=
  R.replacement.oEquivalent

theorem rCellCount_eq : R.diagram.rCellCount = Delta.rCellCount :=
  R.cellMap.orderedTransport.rCellCount_eq

/-- Reducedness survives the deletion. -/
theorem reduced (hred : Delta.Reduced) : R.diagram.Reduced :=
  R.cellMap.orderedTransport.reduced hred

/-- Legal labels stay legal: every label of the deletion is an old label. -/
theorem labelLegal (E : RelGenSet G Lambda) (h : ∀ d, E.IsLetter (Delta.label d))
    (x : R.diagram.toCombMap.Dart) : E.IsLetter (R.diagram.label x) :=
  h (R.val x)

end SpikeDeletion

end GroupApproximation.GGT.VanKampen.Surgery

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.shrunkFace_value
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.face_cases
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.faceOf_keep
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.faceBoundary_kept_map_val
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.shrunk_darts
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.shrunk_not_relatorFace
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.faceCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.dartCount_add_two
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.boundaryWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.cellMap
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.oEquivalent
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.SpikeDeletion.labelLegal
