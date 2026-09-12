import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.GGT.VanKampen.CombMapReduction
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.Meta.AxiomGuard

set_option linter.unusedSectionVars false

/-!
# Transporting a disc diagram to a new map with the same faces

Folds and spur deletions change the combinatorial map of a disc diagram without
changing its faces: each old face has a transported enumeration by darts of the new
map, and those enumerations account for every new dart.  `DiscTransport` records
exactly this data, together with the new labels.

* Every face word other than the exterior one is kept letter for letter, so the
  stored relator cells, conjugators and orientations are kept.
* The exterior word keeps its value, so the stored product formula carries over.
* `DiscTransport.faceEquiv`: the transported enumerations identify old faces with
  new faces, by surjectivity and the face count.
* `DiscTransport.diagram`: the new disc diagram, with `boundaryWord_eq`,
  `rCellCount_eq` and `cover`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- Change the face index of a face boundary along an equality. -/
def FaceBoundary.congr {M : CombMap.{v}} {f f' : M.Face} (B : FaceBoundary M f) (h : f = f') :
    FaceBoundary M f' where
  darts := B.darts
  nonempty := B.nonempty
  nodup := B.nodup
  mem_iff d := (B.mem_iff d).trans (by rw [h])
  chain := B.chain
  closes := B.closes
  length_eq_degree := by rw [← h]; exact B.length_eq_degree

theorem FaceBoundary.congr_darts {M : CombMap.{v}} {f f' : M.Face} (B : FaceBoundary M f)
    (h : f = f') : (B.congr h).darts = B.darts := rfl

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- **Surgery data with the same faces.** -/
structure DiscTransport (Delta : DiscDiagram.{u, w, v} W) where
  /-- The new map. -/
  map : CombMap.{v}
  planar : map.IsPlanar
  /-- The new labels. -/
  label : map.Dart → RelLetter G Lambda
  label_alpha : ∀ d, label (map.alpha d) = HullSC.RelWord.inv (label d)
  /-- The transported enumeration of each old face. -/
  walk : Delta.toCombMap.Face → List map.Dart
  isFaceCycle : ∀ g, map.IsFaceCycle (walk g)
  /-- Inner face words are kept letter for letter. -/
  word : ∀ g, g ≠ Delta.outerFace → (walk g).map label = Delta.faceWord g
  /-- The exterior word keeps its value. -/
  outer_value : RelLetter.listVal ((walk Delta.outerFace).map label) =
    RelLetter.listVal (Delta.faceWord Delta.outerFace)
  /-- Every new dart is on a transported enumeration. -/
  cover : ∀ x : map.Dart, ∃ g, x ∈ walk g
  faceCount_eq : map.faceCount = Delta.toCombMap.faceCount

namespace DiscTransport

variable {Delta : DiscDiagram.{u, w, v} W} (T : DiscTransport Delta)

/-- The new face of an old face. -/
def face (g : Delta.toCombMap.Face) : T.map.Face :=
  T.map.faceOf ((T.walk g).head (T.isFaceCycle g).ne_nil)

theorem face_surjective : Function.Surjective T.face := by
  intro f
  obtain ⟨x, hx⟩ := Quotient.exists_rep f
  obtain ⟨g, hg⟩ := T.cover x
  refine ⟨g, ?_⟩
  have h := ((T.isFaceCycle g).mem_iff x).mp hg
  exact h.symm.trans hx

theorem face_bijective : Function.Bijective T.face := by
  classical
  refine (Fintype.bijective_iff_surjective_and_card T.face).mpr ⟨T.face_surjective, ?_⟩
  have h := T.faceCount_eq
  rw [CombMap.faceCount, CombMap.faceCount, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card] at h
  exact h.symm

/-- **Old faces are new faces.** -/
noncomputable def faceEquiv : Delta.toCombMap.Face ≃ T.map.Face :=
  Equiv.ofBijective T.face T.face_bijective

theorem faceEquiv_apply (g : Delta.toCombMap.Face) : T.faceEquiv g = T.face g := rfl

theorem face_injective : Function.Injective T.face := T.face_bijective.1

/-- The new face boundaries. -/
noncomputable def faceBoundary (f : T.map.Face) : FaceBoundary T.map f :=
  (T.isFaceCycle (T.faceEquiv.symm f)).toFaceBoundary.congr (T.faceEquiv.apply_symm_apply f)

theorem faceBoundary_darts (f : T.map.Face) :
    (T.faceBoundary f).darts = T.walk (T.faceEquiv.symm f) := rfl

theorem faceBoundary_face_darts (g : Delta.toCombMap.Face) :
    (T.faceBoundary (T.face g)).darts = T.walk g := by
  rw [faceBoundary_darts, ← faceEquiv_apply, Equiv.symm_apply_apply]

/-- A relator cell of the new diagram. -/
def cell (C : RelatorCell Delta.toCombMap Delta.outerFace W) :
    RelatorCell T.map (T.face Delta.outerFace) W where
  face := T.face C.face
  face_ne_outer := fun h => C.face_ne_outer (T.face_injective h)
  word := C.word
  word_mem := C.word_mem
  conjugator := C.conjugator
  reversed := C.reversed

/-- **The transported disc diagram.** -/
noncomputable def diagram : DiscDiagram.{u, w, v} W where
  toCombMap := T.map
  planar := T.planar
  label := T.label
  label_alpha := T.label_alpha
  outerFace := T.face Delta.outerFace
  faceBoundary := T.faceBoundary
  relatorCells := Delta.relatorCells.map T.cell
  relatorCell_faces_nodup := by
    have heq : (Delta.relatorCells.map T.cell).map RelatorCell.face =
        (Delta.relatorCells.map RelatorCell.face).map T.face := by
      rw [List.map_map, List.map_map]
      rfl
    rw [heq]
    exact Delta.relatorCell_faces_nodup.map T.face_injective
  relatorCell_word := by
    intro C hC
    obtain ⟨C₀, hC₀, rfl⟩ := List.mem_map.mp hC
    show C₀.word = (T.faceBoundary (T.face C₀.face)).darts.map T.label
    rw [T.faceBoundary_face_darts, T.word C₀.face C₀.face_ne_outer]
    exact Delta.relatorCell_word C₀ hC₀
  inner_face := by
    intro f hf
    have hg : T.faceEquiv.symm f ≠ Delta.outerFace := by
      intro h
      apply hf
      rw [← T.faceEquiv.apply_symm_apply f, h]
      rfl
    rcases Delta.inner_face (T.faceEquiv.symm f) hg with ⟨C, hC, hCg⟩ | htriv
    · left
      refine ⟨T.cell C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
      show T.face C.face = f
      rw [hCg, ← faceEquiv_apply, Equiv.apply_symm_apply]
    · right
      rw [T.faceBoundary_darts, T.word _ hg]
      exact htriv
  boundary_product := by
    have hvalues : (Delta.relatorCells.map T.cell).map RelatorCell.value =
        Delta.relatorCells.map RelatorCell.value := by
      rw [List.map_map]
      rfl
    rw [hvalues, Delta.boundary_product, HullSC.RelWord.listVal_revInv,
      HullSC.RelWord.listVal_revInv]
    show (RelLetter.listVal (Delta.faceWord Delta.outerFace))⁻¹ =
      (RelLetter.listVal ((T.faceBoundary (T.face Delta.outerFace)).darts.map T.label))⁻¹
    rw [T.faceBoundary_face_darts, T.outer_value]

theorem diagram_outerWord :
    T.diagram.faceWord T.diagram.outerFace = (T.walk Delta.outerFace).map T.label := by
  show (T.faceBoundary (T.face Delta.outerFace)).darts.map T.label = _
  rw [T.faceBoundary_face_darts]

/-- **The boundary of the transported diagram.** -/
theorem boundaryWord_eq :
    T.diagram.boundaryWord = HullSC.RelWord.revInv ((T.walk Delta.outerFace).map T.label) := by
  rw [DiscDiagram.boundaryWord, diagram_outerWord]

/-- **The relator area is unchanged.** -/
theorem rCellCount_eq : T.diagram.rCellCount = Delta.rCellCount := by
  show (Delta.relatorCells.map T.cell).length = Delta.relatorCells.length
  exact List.length_map _

/-- **Relator coverage is preserved.** -/
theorem cover_diagram (hcover : RelatorCellCover Delta) : RelatorCellCover T.diagram := by
  constructor
  intro f hf
  have hg : T.faceEquiv.symm f ≠ Delta.outerFace := by
    intro h
    apply hf
    rw [← T.faceEquiv.apply_symm_apply f, h]
    rfl
  obtain ⟨C, hC, hCg⟩ := hcover.cell _ hg
  refine ⟨T.cell C, List.mem_map.mpr ⟨C, hC, rfl⟩, ?_⟩
  show T.face C.face = f
  rw [hCg, ← faceEquiv_apply, Equiv.apply_symm_apply]

end DiscTransport

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscTransport.face_bijective
#audit_axioms GroupApproximation.GGT.VanKampen.DiscTransport.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.DiscTransport.boundaryWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.DiscTransport.rCellCount_eq
#audit_axioms GroupApproximation.GGT.VanKampen.DiscTransport.cover_diagram
