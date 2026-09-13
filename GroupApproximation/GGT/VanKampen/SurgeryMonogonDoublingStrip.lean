import GroupApproximation.GGT.VanKampen.SurgeryMonogonDoubling
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarAssembly
import GroupApproximation.GGT.VanKampen.CombMapEdgeSteps
import GroupApproximation.GGT.VanKampen.FaceCycle
import GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# The strip on a monogon side

Stage 1 of the collar insertion (`GeodesicCollar.StripStatement`) passes to a strip along a side
`s` of a face set `S`: a G-face enumerated by `s ++ q` whose darts `q` cross into `S`.  When
`s = [d]`, the rest is empty and the face `f` of `d` is a monogon, `FaceEdgeDoubling` does not
apply, and the same-corner doubling `MonogonDoubling.diagram` gives the strip instead
(`MonogonStripStatement`, `monogonStrip`).

The digon `[some none, d]` is a G-face (`digon_not_cell`) with the face cycle `[d, some none]`
(`isFaceCycle_digon`), and `some none` crosses into the monogon of the new dart, which stays in
the face set.  The new face set is the image of `S` together with the digon (`faceSet`).  Its only
boundary dart is `d` (`isBoundaryDart_faceSet_iff`), which is still a loop
(`isSimpleClosedWalk_embed_dart`).  The outer boundary and the relator cells outside `S` keep
their darts (`outerDarts_diagram`, `cellDarts_cellIndex`), and every relator cell stays on its
side (`cell_mem_faceSet_iff`).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.MonogonDoubling

open HullSC EdgeInsertion Surgery
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)

/-- The dart of a monogon is fixed by the face rotation. -/
theorem facePerm_dart (hmono : (Delta.faceBoundary f).darts.length = 1) :
    Delta.toCombMap.facePerm (dart Delta f) = dart Delta f :=
  (dart_eq_of_face Delta f hmono
    ((Delta.toCombMap.faceOf_facePerm (dart Delta f)).trans (dart_face Delta f))).symm

/-- The old dart runs into the reverse of the new dart. -/
theorem facePerm_embed_dart (hmono : (Delta.faceBoundary f).darts.length = 1) :
    (map Delta f).facePerm (embed Delta.toCombMap (dart Delta f)) = some none :=
  facePerm_embed_left Delta.toCombMap _ _ (dart Delta f) (facePerm_dart Delta f hmono)

/-- The reverse of the new dart runs into the old dart. -/
theorem facePerm_some_none :
    (map Delta f).facePerm (some none) = embed Delta.toCombMap (dart Delta f) :=
  facePerm_positive Delta.toCombMap _ _

/-- The new dart closes its monogon. -/
theorem facePerm_none : (map Delta f).facePerm none = none :=
  facePerm_none_of_eq Delta.toCombMap (dart Delta f)

/-- **The digon as a face cycle**, starting at the old dart. -/
theorem isFaceCycle_digon (hmono : (Delta.faceBoundary f).darts.length = 1) :
    (map Delta f).IsFaceCycle [embed Delta.toCombMap (dart Delta f), some none] :=
  { ne_nil := List.cons_ne_nil _ _
    nodup := List.nodup_cons.mpr
      ⟨(fun h => by cases List.mem_singleton.mp h), List.nodup_singleton _⟩
    chain := List.isChain_pair.mpr (facePerm_embed_dart Delta f hmono)
    closes := facePerm_some_none Delta f }

/-- The old dart of the monogon is still a loop: the vertex rotation runs from its reverse through
`some none` and `none` back to it. -/
theorem vertexOf_alpha_embed_dart (hmono : (Delta.faceBoundary f).darts.length = 1) :
    (map Delta f).vertexOf ((map Delta f).alpha (embed Delta.toCombMap (dart Delta f))) =
      (map Delta f).vertexOf (embed Delta.toCombMap (dart Delta f)) := by
  have h1 : (map Delta f).sigma ((map Delta f).alpha (embed Delta.toCombMap (dart Delta f))) =
      some none := facePerm_embed_dart Delta f hmono
  have h2 : (map Delta f).sigma (some none) = none := facePerm_none Delta f
  have h3 : (map Delta f).sigma none = embed Delta.toCombMap (dart Delta f) :=
    facePerm_some_none Delta f
  rw [CombMap.vertexOf_eq_iff]
  refine Equiv.Perm.sameCycle_apply_left.mp ?_
  rw [h1]
  refine Equiv.Perm.sameCycle_apply_left.mp ?_
  rw [h2]
  refine Equiv.Perm.sameCycle_apply_left.mp ?_
  exact (congrArg (fun x => (map Delta f).sigma.SameCycle x
    (embed Delta.toCombMap (dart Delta f))) h3).mpr (Equiv.Perm.SameCycle.refl _ _)

/-- **The old dart of the monogon is a simple closed walk.** -/
theorem isSimpleClosedWalk_embed_dart (hmono : (Delta.faceBoundary f).darts.length = 1) :
    IsSimpleClosedWalk (map Delta f) [embed Delta.toCombMap (dart Delta f)] :=
  { ne_nil := List.cons_ne_nil _ _
    chain := List.isChain_singleton _
    closes := vertexOf_alpha_embed_dart Delta f hmono
    vertex_nodup := List.nodup_singleton _
    alpha_not_mem := fun e he h => by
      obtain rfl := List.mem_singleton.mp he
      exact (map Delta f).alpha_fixedPointFree _ (List.mem_singleton.mp h) }

theorem faceOf_none : (map Delta f).faceOf none = cellFace Delta f :=
  ((boundary Delta f (cellFace Delta f)).mem_iff _).mp (by
    rw [boundary_cellFace]
    exact List.mem_singleton_self _)

theorem faceOf_some_none : (map Delta f).faceOf (some none) = digon Delta f :=
  ((boundary Delta f (digon Delta f)).mem_iff _).mp (by
    rw [boundary_digon]
    exact List.mem_cons_self)

/-- The old darts of the face `f` lie in the digon. -/
theorem faceOf_embed_of_face {e : Delta.toCombMap.Dart} (he : Delta.toCombMap.faceOf e = f) :
    (map Delta f).faceOf (embed Delta.toCombMap e) = digon Delta f :=
  ((boundary Delta f (digon Delta f)).mem_iff _).mp (by
    rw [boundary_digon]
    exact List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨e, ((Delta.faceBoundary f).mem_iff e).mpr he, rfl⟩))

theorem faceOf_embed_of_ne {e : Delta.toCombMap.Dart} (he : Delta.toCombMap.faceOf e ≠ f) :
    (map Delta f).faceOf (embed Delta.toCombMap e) = keep Delta f (Delta.toCombMap.faceOf e) :=
  ((boundary Delta f (keep Delta f (Delta.toCombMap.faceOf e))).mem_iff _).mp (by
    rw [boundary_kept Delta f he]
    exact List.mem_map.mpr ⟨e, ((Delta.faceBoundary _).mem_iff e).mpr rfl, rfl⟩)

/-- **The face set after the doubling**: the images of the old faces, and the digon. -/
noncomputable def faceSet (S : Finset Delta.toCombMap.Face) : Finset (map Delta f).Face :=
  insert (digon Delta f) (S.map ⟨faceImage Delta f, faceImage_injective Delta f⟩)

theorem mem_faceSet_faceImage (S : Finset Delta.toCombMap.Face) (g : Delta.toCombMap.Face) :
    faceImage Delta f g ∈ faceSet Delta f S ↔ g ∈ S := by
  rw [faceSet, Finset.mem_insert]
  exact (or_iff_right (faceImage_ne_digon Delta f g)).trans
    (Finset.mem_map' ⟨faceImage Delta f, faceImage_injective Delta f⟩)

theorem faceOf_some_none_mem (S : Finset Delta.toCombMap.Face) :
    (map Delta f).faceOf (some none) ∈ faceSet Delta f S := by
  rw [faceOf_some_none, faceSet, Finset.mem_insert]
  exact Or.inl rfl

/-- The reverse of `some none` lies in the monogon of the new dart, which is in the face set. -/
theorem faceOf_alpha_some_none_mem {S : Finset Delta.toCombMap.Face} (hS : f ∈ S) :
    (map Delta f).faceOf ((map Delta f).alpha (some none)) ∈ faceSet Delta f S := by
  change (map Delta f).faceOf none ∈ faceSet Delta f S
  rw [faceOf_none, ← faceImage_self Delta f]
  exact (mem_faceSet_faceImage Delta f S f).mpr hS

/-- An old dart lies in the new face set exactly when it lay in the old one. -/
theorem faceOf_embed_mem_faceSet_iff {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (e : Delta.toCombMap.Dart) :
    (map Delta f).faceOf (embed Delta.toCombMap e) ∈ faceSet Delta f S ↔
      Delta.toCombMap.faceOf e ∈ S := by
  by_cases he : Delta.toCombMap.faceOf e = f
  · rw [faceOf_embed_of_face Delta f he, he, faceSet, Finset.mem_insert]
    exact iff_of_true (Or.inl rfl) hS
  · rw [faceOf_embed_of_ne Delta f he, ← faceImage_of_ne Delta f he]
    exact mem_faceSet_faceImage Delta f S _

theorem isBoundaryDart_embed_iff {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (e : Delta.toCombMap.Dart) :
    MapCollapse.IsBoundaryDart (map Delta f) (faceSet Delta f S) (embed Delta.toCombMap e) ↔
      MapCollapse.IsBoundaryDart Delta.toCombMap S e :=
  and_congr (faceOf_embed_mem_faceSet_iff Delta f hS e)
    (not_congr (faceOf_embed_mem_faceSet_iff Delta f hS (Delta.toCombMap.alpha e)))

/-- **The boundary of the new face set is the old dart.** -/
theorem isBoundaryDart_faceSet_iff {S : Finset Delta.toCombMap.Face} (hS : f ∈ S)
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ [dart Delta f])
    (x : (map Delta f).Dart) :
    MapCollapse.IsBoundaryDart (map Delta f) (faceSet Delta f S) x ↔
      x ∈ [embed Delta.toCombMap (dart Delta f)] := by
  rcases x with _ | (_ | e)
  · refine iff_of_false (fun h => h.2 ?_) (fun h => by cases List.mem_singleton.mp h)
    exact faceOf_some_none_mem Delta f S
  · refine iff_of_false (fun h => h.2 ?_) (fun h => by cases List.mem_singleton.mp h)
    exact faceOf_alpha_some_none_mem Delta f hS
  · refine (isBoundaryDart_embed_iff Delta f hS e).trans ((hB e).trans ?_)
    exact ⟨fun h => List.mem_singleton.mpr
        (congrArg (embed Delta.toCombMap) (List.mem_singleton.mp h)),
      fun h => List.mem_singleton.mpr (embed_injective Delta.toCombMap (List.mem_singleton.mp h))⟩

section Diagram

variable (hf : f ≠ Delta.outerFace) (hmono : (Delta.faceBoundary f).darts.length = 1)

theorem outerFace_not_mem_faceSet {S : Finset Delta.toCombMap.Face}
    (hout : Delta.outerFace ∉ S) :
    (diagram Delta f hf hmono).outerFace ∉ faceSet Delta f S := by
  change keep Delta f Delta.outerFace ∉ faceSet Delta f S
  rw [← faceImage_of_ne Delta f hf.symm, mem_faceSet_faceImage]
  exact hout

/-- **The digon is a G-face.** -/
theorem digon_not_cell :
    ∀ C ∈ (diagram Delta f hf hmono).relatorCells, C.face ≠ digon Delta f := by
  intro C hC
  change C ∈ Delta.relatorCells.map (cell Delta f hf) at hC
  obtain ⟨C₀, _, rfl⟩ := List.mem_map.mp hC
  exact faceImage_ne_digon Delta f C₀.face

theorem cell_face_cellIndex (i : Fin Delta.rCellCount) :
    (Embedded.cell (diagram Delta f hf hmono) ((oEquivalent Delta f hf hmono).cellIndex i)).face =
      faceImage Delta f (Embedded.cell Delta i).face := by
  change (Embedded.cell (diagram Delta f hf hmono)
    ((cellMap Delta f hf hmono).indexEquiv i)).face = _
  rw [(cellMap Delta f hf hmono).indexed_cell, (cellMap Delta f hf hmono).face_eq]

/-- **A relator cell away from the monogon keeps its darts.** -/
theorem cellDarts_cellIndex {i : Fin Delta.rCellCount} (hi : (Embedded.cell Delta i).face ≠ f) :
    Embedded.cellDarts (diagram Delta f hf hmono) ((oEquivalent Delta f hf hmono).cellIndex i) =
      (Embedded.cellDarts Delta i).map (embed Delta.toCombMap) := by
  change ((diagram Delta f hf hmono).faceBoundary (Embedded.cell (diagram Delta f hf hmono)
    ((oEquivalent Delta f hf hmono).cellIndex i)).face).darts = _
  rw [cell_face_cellIndex Delta f hf hmono i, faceImage_of_ne Delta f hi]
  exact boundary_kept Delta f hi

/-- **Every relator cell stays on its side of the face set.** -/
theorem cell_mem_faceSet_iff (S : Finset Delta.toCombMap.Face) (i : Fin Delta.rCellCount) :
    (Embedded.cell (diagram Delta f hf hmono) ((oEquivalent Delta f hf hmono).cellIndex i)).face ∈
        faceSet Delta f S ↔ (Embedded.cell Delta i).face ∈ S := by
  rw [cell_face_cellIndex Delta f hf hmono i]
  exact mem_faceSet_faceImage Delta f S _

/-- **The outer boundary keeps its darts.** -/
theorem outerDarts_diagram :
    Embedded.outerDarts (diagram Delta f hf hmono) =
      (Embedded.outerDarts Delta).map (embed Delta.toCombMap) :=
  (embedding Delta f hf hmono).outerDarts_eq hf

/-- **The transport of the doubling** from a face set containing the monogon. -/
noncomputable def collarTransport (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hlabel : ∀ d, D.IsLetter (Delta.label d)) {S : Finset Delta.toCombMap.Face} (hS : f ∈ S) :
    GeodesicCollar.Transport D S (diagram Delta f hf hmono) (faceSet Delta f S) where
  equiv := oEquivalent Delta f hf hmono
  embedding := ⟨embed Delta.toCombMap, embed_injective Delta.toCombMap⟩
  label_isLetter := label_admissible Delta f hf hmono D hsymm hlabel
  alpha_embedding _ := rfl
  label_embedding _ := rfl
  outerDarts_eq := outerDarts_diagram Delta f hf hmono
  cellDarts_eq _ hi := cellDarts_cellIndex Delta f hf hmono (fun h => hi (by rw [h]; exact hS))
  cell_mem_iff i := cell_mem_faceSet_iff Delta f hf hmono S i

/-- **The strip on the monogon side** `[d]`: the digon `[d, some none]`. -/
noncomputable def collarStrip {S : Finset Delta.toCombMap.Face} {d : Delta.toCombMap.Dart}
    (hd : Delta.toCombMap.faceOf d = f)
    (hB : ∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ [d] ++ [])
    (hout : Delta.outerFace ∉ S) :
    GeodesicCollar.Strip (diagram Delta f hf hmono) (faceSet Delta f S)
      [embed Delta.toCombMap d] [] := by
  obtain rfl := dart_eq_of_face Delta f hmono hd
  have hS : f ∈ S := by
    have h := ((hB (dart Delta f)).mpr (List.mem_singleton_self _)).1
    rwa [dart_face Delta f] at h
  exact
    { q := [some none]
      p_ne_nil := List.cons_ne_nil _ _
      q_ne_nil := List.cons_ne_nil _ _
      cycle := isFaceCycle_digon Delta f hmono
      not_cell := fun C hC h => digon_not_cell Delta f hf hmono C hC
        (h.trans (faceOf_embed_of_face Delta f (dart_face Delta f)))
      alpha_mem := fun e he => by
        obtain rfl := List.mem_singleton.mp he
        exact faceOf_alpha_some_none_mem Delta f hS
      walk := isSimpleClosedWalk_embed_dart Delta f hmono
      boundary := isBoundaryDart_faceSet_iff Delta f hS hB
      outerFace_not_mem := outerFace_not_mem_faceSet Delta f hf hmono hout }

end Diagram

/-- **Stage 1 of the collar insertion on a monogon side.**  `GeodesicCollar.StripStatement` for
the side `s = [d]` with `rest = []` when the face of `d` is a monogon, where `FaceEdgeDoubling`
does not apply.  The walk hypothesis is dropped: a monogon dart is a loop. -/
def MonogonStripStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (D : RelGenSet G Lambda), (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ (Delta : DiscDiagram.{u, w, v} W), (∀ d, D.IsLetter (Delta.label d)) →
    ∀ (S : Finset Delta.toCombMap.Face) (d : Delta.toCombMap.Dart),
      (Delta.faceBoundary (Delta.toCombMap.faceOf d)).darts.length = 1 →
      (∀ e, MapCollapse.IsBoundaryDart Delta.toCombMap S e ↔ e ∈ [d] ++ []) →
      Delta.outerFace ∉ S →
      ∃ (Delta' : DiscDiagram.{u, w, v} W) (S' : Finset Delta'.toCombMap.Face)
        (T : GeodesicCollar.Transport D S Delta' S'),
        Nonempty (GeodesicCollar.Strip Delta' S' ([d].map T.embedding)
          (([] : List Delta.toCombMap.Dart).map T.embedding))

theorem monogonStrip : MonogonStripStatement.{u, w, v} := by
  intro G _ Lambda W D hsymm Delta hlabel S d hmono hB hout
  have hS : Delta.toCombMap.faceOf d ∈ S := ((hB d).mpr (List.mem_singleton_self d)).1
  have hf : Delta.toCombMap.faceOf d ≠ Delta.outerFace :=
    fun h => hout (by rw [← h]; exact hS)
  exact ⟨diagram Delta (Delta.toCombMap.faceOf d) hf hmono,
    faceSet Delta (Delta.toCombMap.faceOf d) S,
    collarTransport Delta (Delta.toCombMap.faceOf d) hf hmono D hsymm hlabel hS,
    ⟨collarStrip Delta (Delta.toCombMap.faceOf d) hf hmono rfl hB hout⟩⟩

end GroupApproximation.GGT.VanKampen.MonogonDoubling

#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.isFaceCycle_digon
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.isSimpleClosedWalk_embed_dart
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.isBoundaryDart_faceSet_iff
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.outerFace_not_mem_faceSet
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.digon_not_cell
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.cellDarts_cellIndex
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.cell_mem_faceSet_iff
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.outerDarts_diagram
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.collarTransport
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.collarStrip
#audit_axioms GroupApproximation.GGT.VanKampen.MonogonDoubling.monogonStrip
