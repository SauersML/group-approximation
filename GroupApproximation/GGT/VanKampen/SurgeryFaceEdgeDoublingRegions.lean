import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoubling
import GroupApproximation.GGT.VanKampen.GFaceQuadrilateralRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Region families through the doubling of an edge

`FaceEdgeDoubling.diagram` inserts a digon inside an inner face `f` along a dart `w_j`.
Every old dart survives (`EdgeInsertion.embed`) and every face other than `f` keeps its
traversal, so the landed boundary and shelling transport of `DiscEmbeddingAway` applies to
any region avoiding `f` (`embedding`).  The one difference from a G-face insertion is the
relator carrier of `f`: in it the new dart stands in the place of `w_j`
(`boundary_cellFace_darts`).

A region that avoids `f` and the face across `w_j` never uses `w_j` in a contiguity arc:
the reverse of an arc dart lies on the region's boundary cycle
(`dart_not_mem_sourceArc`, `dart_not_mem_targetArc`).  So its arcs transport through the
carrier maps (`carrierImage`, `targetImage`) with the same darts as through `embed`, and
the whole contiguity geometry transports (`contiguityGeometry`).  A compatible family of
such regions is retained with its card, weight and target profiles (`regionFamily`).
-/

namespace GroupApproximation.GGT.VanKampen.FaceEdgeDoubling

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

theorem dart_face : Delta.toCombMap.faceOf (dart Delta f j) = f :=
  firstCorner_face Delta.toCombMap (rebased Delta f j)

/-- The retained old darts and faces. -/
noncomputable def embedding : DiscEmbeddingAway Delta (diagram Delta f j hlen hf) f where
  darts := ⟨embed Delta.toCombMap, embed_injective Delta.toCombMap⟩
  faces := ⟨keep Delta f j hlen, keep_injective Delta f j hlen⟩
  alpha _ := rfl
  label _ := rfl
  outer := rfl
  face_boundary _ hg := boundary_kept Delta f j hlen hg
  facePerm d hd := facePerm_embed_of_ne Delta.toCombMap _ _ d
    (corners_face_eq Delta.toCombMap (rebased Delta f j) (second Delta f j hlen))
    (by rwa [firstCorner_face Delta.toCombMap (rebased Delta f j)])

/-- The dart map on the traversal of an old face. -/
noncomputable def carrierImage (g : Delta.toCombMap.Face) :
    Delta.toCombMap.Dart → (diagram Delta f j hlen hf).toCombMap.Dart :=
  if g = f then dartImage Delta f j hlen else embed Delta.toCombMap

theorem carrierImage_of_ne_dart (g : Delta.toCombMap.Face) {d : Delta.toCombMap.Dart}
    (hd : d ≠ dart Delta f j) :
    carrierImage Delta f j hlen hf g d = (embedding Delta f j hlen hf).darts d := by
  unfold carrierImage
  split_ifs
  · change dartImage Delta f j hlen d = embed Delta.toCombMap d
    rw [dartImage, if_neg hd]
  · rfl

theorem carrierImage_self :
    carrierImage Delta f j hlen hf f = dartImage Delta f j hlen := if_pos rfl

theorem carrierImage_of_ne {g : Delta.toCombMap.Face} (hg : g ≠ f) :
    carrierImage Delta f j hlen hf g = embed Delta.toCombMap := if_neg hg

theorem boundary_faceImage_darts (g : Delta.toCombMap.Face) :
    ((diagram Delta f j hlen hf).faceBoundary (faceImage Delta f j hlen g)).darts =
      (Delta.faceBoundary g).darts.map (carrierImage Delta f j hlen hf g) := by
  by_cases hg : g = f
  · subst hg
    exact (congrArg (fun F => (boundary Delta g j hlen F).darts) (faceImage_self Delta g j hlen)).trans
      ((boundary_cellFace_darts Delta g j hlen).trans
        (congrArg (fun φ => (Delta.faceBoundary g).darts.map φ)
          (carrierImage_self Delta g j hlen hf).symm))
  · exact (congrArg (fun F => (boundary Delta f j hlen F).darts)
      (faceImage_of_ne Delta f j hlen hg)).trans
      ((boundary_kept Delta f j hlen hg).trans
        (congrArg (fun φ => (Delta.faceBoundary g).darts.map φ)
          (carrierImage_of_ne Delta f j hlen hf hg).symm))

theorem cellDarts_eq (i : Fin Delta.rCellCount) :
    cellDarts (diagram Delta f j hlen hf) ((cellMap Delta f j hlen hf).indexEquiv i) =
      (cellDarts Delta i).map
        (carrierImage Delta f j hlen hf (Embedded.cell Delta i).face) := by
  change ((diagram Delta f j hlen hf).faceBoundary
    (Embedded.cell (diagram Delta f j hlen hf)
      ((cellMap Delta f j hlen hf).indexEquiv i)).face).darts = _
  rw [(cellMap Delta f j hlen hf).indexed_cell, (cellMap Delta f j hlen hf).face_eq]
  exact boundary_faceImage_darts Delta f j hlen hf (Embedded.cell Delta i).face

/-- The dart map on the carrier of a target. -/
noncomputable def targetImage : Option (Fin Delta.rCellCount) →
    Delta.toCombMap.Dart → (diagram Delta f j hlen hf).toCombMap.Dart
  | none => (embedding Delta f j hlen hf).darts
  | some i => carrierImage Delta f j hlen hf (Embedded.cell Delta i).face

theorem targetImage_of_ne_dart (t : Option (Fin Delta.rCellCount)) {d : Delta.toCombMap.Dart}
    (hd : d ≠ dart Delta f j) :
    targetImage Delta f j hlen hf t d = (embedding Delta f j hlen hf).darts d := by
  cases t with
  | none => rfl
  | some i => exact carrierImage_of_ne_dart Delta f j hlen hf _ hd

theorem targetDarts_eq (t : Option (Fin Delta.rCellCount)) :
    targetDarts (diagram Delta f j hlen hf) (t.map (cellMap Delta f j hlen hf).indexEquiv) =
      (targetDarts Delta t).map (targetImage Delta f j hlen hf t) := by
  cases t with
  | none => exact (embedding Delta f j hlen hf).outerDarts_eq hf
  | some i => exact cellDarts_eq Delta f j hlen hf i

theorem mapTo_darts_of_avoid {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle)
    (g : Delta.toCombMap.Dart → (diagram Delta f j hlen hf).toCombMap.Dart)
    (hg : ∀ d, d ≠ dart Delta f j → g d = (embedding Delta f j hlen hf).darts d)
    {target : List (diagram Delta f j hlen hf).toCombMap.Dart} (h : target = cycle.map g)
    (havoid : dart Delta f j ∉ arc.darts) :
    (arc.mapTo g h).darts = arc.darts.map (embedding Delta f j hlen hf).darts := by
  rw [CyclicArc.mapTo_darts]
  exact List.map_congr_left (fun d hd => hg d (fun heq => havoid (heq ▸ hd)))

theorem reverseDarts_of_avoid {cycle : List Delta.toCombMap.Dart} (arc : CyclicArc cycle)
    (g : Delta.toCombMap.Dart → (diagram Delta f j hlen hf).toCombMap.Dart)
    (hg : ∀ d, d ≠ dart Delta f j → g d = (embedding Delta f j hlen hf).darts d)
    {target : List (diagram Delta f j hlen hf).toCombMap.Dart} (h : target = cycle.map g)
    (havoid : dart Delta f j ∉ arc.darts) :
    (arc.mapTo g h).reverseDarts = arc.reverseDarts.map (embedding Delta f j hlen hf).darts := by
  change invDarts (diagram Delta f j hlen hf) (arc.mapTo g h).darts =
    (invDarts Delta arc.darts).map (embedding Delta f j hlen hf).darts
  rw [mapTo_darts_of_avoid Delta f j hlen hf arc g hg h havoid]
  exact (embedding Delta f j hlen hf).invDarts_map arc.darts

theorem targetBoundaryDarts_transport (t : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta t)) (havoid : dart Delta f j ∉ arc.darts) :
    targetBoundaryDarts (diagram Delta f j hlen hf) (t.map (cellMap Delta f j hlen hf).indexEquiv)
        (arc.mapTo (targetImage Delta f j hlen hf t) (targetDarts_eq Delta f j hlen hf t)) =
      (targetBoundaryDarts Delta t arc).map (embedding Delta f j hlen hf).darts := by
  cases t with
  | none =>
      exact mapTo_darts_of_avoid Delta f j hlen hf arc _
        (fun _ hd => targetImage_of_ne_dart Delta f j hlen hf none hd) _ havoid
  | some i =>
      exact reverseDarts_of_avoid Delta f j hlen hf arc _
        (fun _ hd => targetImage_of_ne_dart Delta f j hlen hf (some i) hd) _ havoid

theorem mem_targetBoundaryDarts_of_mem (t : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta t)) {d : Delta.toCombMap.Dart} (hd : d ∈ arc.darts) :
    d ∈ targetBoundaryDarts Delta t arc ∨
      Delta.toCombMap.alpha d ∈ targetBoundaryDarts Delta t arc := by
  cases t with
  | none => exact Or.inl hd
  | some i => exact Or.inr (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩)

/-- A region avoiding the face across `w_j` does not use `w_j` in its source arc. -/
theorem dart_not_mem_sourceArc {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (hs2 : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s) :
    dart Delta f j ∉ H.sourceArc.darts := by
  intro hmem
  have hrev : Delta.toCombMap.alpha (dart Delta f j) ∈ H.sourceArc.reverseDarts :=
    List.mem_map.mpr ⟨dart Delta f j, List.mem_reverse.mpr hmem, rfl⟩
  have hcycle : Delta.toCombMap.alpha (dart Delta f j) ∈ H.boundary.cycle := by
    rw [H.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hrev))
  exact hs2 ((H.boundary.cycle_mem_iff _).mp hcycle).1

/-- A region avoiding `f` and the face across `w_j` does not use `w_j` in its target arc. -/
theorem dart_not_mem_targetArc {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s) (hs : f ∉ s)
    (hs2 : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s) :
    dart Delta f j ∉ H.targetArc.darts := by
  intro hmem
  have hcycle : ∀ d ∈ targetBoundaryDarts Delta H.target H.targetArc, d ∈ H.boundary.cycle := by
    intro d hd
    rw [H.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hd)
  rcases mem_targetBoundaryDarts_of_mem Delta H.target H.targetArc hmem with h | h
  · have hin := ((H.boundary.cycle_mem_iff _).mp (hcycle _ h)).1
    rw [dart_face] at hin
    exact hs hin
  · exact hs2 ((H.boundary.cycle_mem_iff _).mp (hcycle _ h)).1

/-- **Contiguity geometry through the doubling.** -/
noncomputable def contiguityGeometry {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (hs2 : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    ContiguityGeometry D eps (diagram Delta f j hlen hf)
      ((embedding Delta f j hlen hf).faceSet s) where
  boundary := (embedding Delta f j hlen hf).boundary s hs H.boundary
  source := (cellMap Delta f j hlen hf).indexEquiv H.source
  target := H.target.map (cellMap Delta f j hlen hf).indexEquiv
  sourceArc := H.sourceArc.mapTo
    (carrierImage Delta f j hlen hf (Embedded.cell Delta H.source).face)
    (cellDarts_eq Delta f j hlen hf H.source)
  targetArc := H.targetArc.mapTo (targetImage Delta f j hlen hf H.target)
    (targetDarts_eq Delta f j hlen hf H.target)
  rightSide := H.rightSide.map (embedding Delta f j hlen hf).darts
  leftSide := H.leftSide.map (embedding Delta f j hlen hf).darts
  boundary_decomposition := by
    change H.boundary.cycle.map (embedding Delta f j hlen hf).darts = _
    rw [reverseDarts_of_avoid Delta f j hlen hf H.sourceArc
        (carrierImage Delta f j hlen hf (Embedded.cell Delta H.source).face)
        (fun _ hd => carrierImage_of_ne_dart Delta f j hlen hf _ hd)
        (cellDarts_eq Delta f j hlen hf H.source)
        (dart_not_mem_sourceArc Delta f j H hs2),
      targetBoundaryDarts_transport Delta f j hlen hf H.target H.targetArc
        (dart_not_mem_targetArc Delta f j H hs hs2)]
    exact (congrArg (List.map (embedding Delta f j hlen hf).darts) H.boundary_decomposition).trans
      (by simp only [List.map_append])
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by
    rw [(embedding Delta f j hlen hf).dartWord_map]
    exact H.rightSide_norm_le
  leftSide_norm_le := by
    rw [(embedding Delta f j hlen hf).dartWord_map]
    exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map (embedding Delta f j hlen hf).faces, (embedding Delta f j hlen hf).shelling s hs hl⟩

theorem contiguityGeometry_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (hs2 : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (contiguityGeometry Delta f j hlen hf hs hs2 H).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length (carrierImage Delta f j hlen hf (Embedded.cell Delta H.source).face)
    (cellDarts_eq Delta f j hlen hf H.source)

theorem contiguityGeometry_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (hs2 : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (contiguityGeometry Delta f j hlen hf hs hs2 H).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length (targetImage Delta f j hlen hf H.target)
    (targetDarts_eq Delta f j hlen hf H.target)

theorem contiguityGeometry_target_start {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (hs2 : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s)
    (H : ContiguityGeometry D eps Delta s) :
    (contiguityGeometry Delta f j hlen hf hs hs2 H).targetArc.start.val =
      H.targetArc.start.val :=
  H.targetArc.mapTo_start (targetImage Delta f j hlen hf H.target)
    (targetDarts_eq Delta f j hlen hf H.target)

theorem contiguityGeometry_injective {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (hs2 : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s) :
    Function.Injective (contiguityGeometry Delta f j hlen hf hs hs2 :
      ContiguityGeometry D eps Delta s → ContiguityGeometry D eps (diagram Delta f j hlen hf)
        ((embedding Delta f j hlen hf).faceSet s)) := by
  intro H K h
  apply ContiguityGeometry.eq_of_data
  · exact (List.map_injective_iff.mpr (embedding Delta f j hlen hf).darts.injective)
      (congrArg (fun J => J.boundary.cycle) h)
  · exact (cellMap Delta f j hlen hf).indexEquiv.injective (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr (cellMap Delta f j hlen hf).indexEquiv).injective
      (congrArg (fun J => J.target) h)
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguityGeometry_source_length] using congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguityGeometry_target_length] using congrArg (fun J => J.targetArc.length) h
  · exact (List.map_injective_iff.mpr (embedding Delta f j hlen hf).darts.injective)
      (congrArg (fun J => J.rightSide) h)
  · exact (List.map_injective_iff.mpr (embedding Delta f j hlen hf).darts.injective)
      (congrArg (fun J => J.leftSide) h)

/-- The regions a doubling retains: those avoiding `f` and the face across `w_j`. -/
abbrev Avoiding (D : RelGenSet G Lambda) (eps : ℕ) :=
  { a : RegionCandidate D eps Delta //
    f ∉ a.1 ∧ Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ a.1 }

noncomputable def regionCandidate {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Avoiding Delta f j D eps) : RegionCandidate D eps (diagram Delta f j hlen hf) :=
  ⟨(embedding Delta f j hlen hf).faceSet a.val.1,
    contiguityGeometry Delta f j hlen hf a.property.1 a.property.2 a.val.2⟩

theorem regionCandidate_injective {D : RelGenSet G Lambda} {eps : ℕ} :
    Function.Injective (regionCandidate Delta f j hlen hf :
      Avoiding Delta f j D eps → RegionCandidate D eps (diagram Delta f j hlen hf)) := by
  rintro ⟨⟨s, H⟩, hs⟩ ⟨⟨t, K⟩, ht⟩ h
  have hfaces : (embedding Delta f j hlen hf).faceSet s =
      (embedding Delta f j hlen hf).faceSet t := congrArg Sigma.fst h
  have hst : s = t := Finset.map_injective (embedding Delta f j hlen hf).faces hfaces
  subst hst
  have hcont : contiguityGeometry Delta f j hlen hf hs.1 hs.2 H =
      contiguityGeometry Delta f j hlen hf ht.1 ht.2 K :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hHK := contiguityGeometry_injective Delta f j hlen hf hs.1 hs.2 hcont
  cases hHK
  rfl

theorem regionCandidate_weight {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Avoiding Delta f j D eps) :
    RegionCandidate.weight (regionCandidate Delta f j hlen hf a) =
      RegionCandidate.weight a.val :=
  congrArg₂ Nat.add
    (contiguityGeometry_source_length Delta f j hlen hf a.property.1 a.property.2 a.val.2)
    (contiguityGeometry_target_length Delta f j hlen hf a.property.1 a.property.2 a.val.2)

theorem regionCandidate_compatible {D : RelGenSet G Lambda} {eps : ℕ}
    (a b : Avoiding Delta f j D eps) :
    RegionCandidate.Compatible (regionCandidate Delta f j hlen hf a)
        (regionCandidate Delta f j hlen hf b) ↔ RegionCandidate.Compatible a.val b.val :=
  (embedding Delta f j hlen hf).faceSet_disjoint_iff a.val.1 b.val.1

theorem regionCandidate_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Avoiding Delta f j D eps) :
    RegionCandidate.SameTargetProfile (regionCandidate Delta f j hlen hf a) a.val :=
  And.intro Option.map_eq_none_iff
    (And.intro (contiguityGeometry_target_start Delta f j hlen hf a.property.1 a.property.2 a.val.2)
      (And.intro
        (contiguityGeometry_target_length Delta f j hlen hf a.property.1 a.property.2 a.val.2)
        (contiguityGeometry_source_length Delta f j hlen hf a.property.1 a.property.2 a.val.2)))

noncomputable def regionFamilyEmbedding {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family,
      f ∉ a.1 ∧ Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ a.1) :
    family ↪ RegionCandidate D eps (diagram Delta f j hlen hf) where
  toFun a := regionCandidate Delta f j hlen hf ⟨a.val, havoid a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : Avoiding Delta f j D eps => x.val)
      (regionCandidate_injective Delta f j hlen hf h)

/-- **A family avoiding `f` and the face across `w_j`, after the doubling.** -/
noncomputable def regionFamily {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family,
      f ∉ a.1 ∧ Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ a.1) :
    Finset (RegionCandidate D eps (diagram Delta f j hlen hf)) :=
  family.attach.map (regionFamilyEmbedding Delta f j hlen hf family havoid)

theorem regionFamily_faces {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family,
      f ∉ a.1 ∧ Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ a.1)
    {a : RegionCandidate D eps (diagram Delta f j hlen hf)}
    (ha : a ∈ regionFamily Delta f j hlen hf family havoid) :
    ∃ b ∈ family, a.1 = (embedding Delta f j hlen hf).faceSet b.1 := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, rfl⟩

theorem regionFamily_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family,
      f ∉ a.1 ∧ Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ a.1)
    {a : RegionCandidate D eps (diagram Delta f j hlen hf)}
    (ha : a ∈ regionFamily Delta f j hlen hf family havoid) :
    ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, regionCandidate_profile Delta f j hlen hf _⟩

theorem regionFamily_card {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family,
      f ∉ a.1 ∧ Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ a.1) :
    (regionFamily Delta f j hlen hf family havoid).card = family.card := by
  simp only [regionFamily, Finset.card_map, Finset.card_attach]

theorem regionFamily_weight {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family,
      f ∉ a.1 ∧ Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ a.1) :
    EstimatingSelection.familyWeight RegionCandidate.weight
        (regionFamily Delta f j hlen hf family havoid) =
      EstimatingSelection.familyWeight RegionCandidate.weight family := by
  unfold EstimatingSelection.familyWeight regionFamily
  rw [Finset.sum_map]
  trans ∑ a ∈ family.attach, RegionCandidate.weight a.val
  · apply Finset.sum_congr rfl
    intro a _
    exact regionCandidate_weight Delta f j hlen hf ⟨a.val, havoid a.val a.property⟩
  · exact Finset.sum_attach _ _

theorem regionFamily_pairwise {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family,
      f ∉ a.1 ∧ Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ a.1)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (regionFamily Delta f j hlen hf family havoid) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (regionCandidate_compatible Delta f j hlen hf
    ⟨a.val, havoid a.val a.property⟩ ⟨b.val, havoid b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (regionFamilyEmbedding Delta f j hlen hf family havoid) (Subtype.ext hab))

end GroupApproximation.GGT.VanKampen.FaceEdgeDoubling

#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.embedding
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.contiguityGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.contiguityGeometry_injective
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.regionFamily_profile
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.regionFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.regionFamily_pairwise
