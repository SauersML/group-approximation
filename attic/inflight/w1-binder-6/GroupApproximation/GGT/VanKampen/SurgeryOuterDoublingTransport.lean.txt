import GroupApproximation.GGT.VanKampen.SurgeryOuterSpurThickening
import GroupApproximation.Meta.AxiomGuard

/-!
# Region families through an outer doubling, along the target arcs

`OuterSpurThickening` doubles an exterior dart `w_j` into a G-cell digon and transports every
region avoiding the face across `w_j`.  The hypothesis enters its contiguity transport at one
place only: the reverse of `w_j` must not lie in the target arc
(`OuterSpurThickening.alpha_dart_not_mem_targetArc`).  This file transports under that weaker
hypothesis, so a region whose side runs along the exterior at `w_j` is transported too.

* `contiguityGeometry`, `regionCandidate`, `regionFamily`, `regionFamilyEquiv`: the transport
  for regions whose target arc does not use `alpha w_j`, with card, weight, compatibility,
  target profiles and source indices kept.
* `alpha_dart_not_mem_targetArc_of_side`: a region with `alpha w_j` as a side dart does not use
  `alpha w_j` in its target arc, because its boundary cycle has no repeated dart.
* `not_mem_targetArc_of_avoid`: the old hypothesis gives the new one.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.OuterDoublingTransport

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

section Transport

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

/-- **Contiguity geometry through an outer doubling**, for a region whose target arc does not
use the reverse of the doubled dart. -/
noncomputable def contiguityGeometry {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (htgt : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      H.targetArc.darts) :
    ContiguityGeometry D eps (OuterSpurThickening.diagram Delta j hlen)
      ((OuterSpurThickening.embedding Delta j hlen).faceSet s) where
  boundary := (OuterSpurThickening.embedding Delta j hlen).boundary s
    (OuterSpurThickening.outer_not_mem Delta H) H.boundary
  source := (OuterSpurThickening.cellMap Delta j hlen).indexEquiv H.source
  target := H.target.map (OuterSpurThickening.cellMap Delta j hlen).indexEquiv
  sourceArc := H.sourceArc.mapTo (OuterSpurThickening.embedding Delta j hlen).darts
    (OuterSpurThickening.cellDarts_eq Delta j hlen H.source)
  targetArc := H.targetArc.mapTo (OuterSpurThickening.targetImage Delta j hlen H.target)
    (OuterSpurThickening.targetDarts_eq Delta j hlen H.target)
  rightSide := H.rightSide.map (OuterSpurThickening.embedding Delta j hlen).darts
  leftSide := H.leftSide.map (OuterSpurThickening.embedding Delta j hlen).darts
  boundary_decomposition := by
    change H.boundary.cycle.map (OuterSpurThickening.embedding Delta j hlen).darts = _
    rw [(OuterSpurThickening.embedding Delta j hlen).reverseDarts_mapTo H.sourceArc
        (OuterSpurThickening.cellDarts_eq Delta j hlen H.source),
      OuterSpurThickening.targetBoundaryDarts_transport Delta j hlen H.target H.targetArc htgt]
    exact (congrArg (List.map (OuterSpurThickening.embedding Delta j hlen).darts)
      H.boundary_decomposition).trans (by simp only [List.map_append])
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by
    rw [(OuterSpurThickening.embedding Delta j hlen).dartWord_map]
    exact H.rightSide_norm_le
  leftSide_norm_le := by
    rw [(OuterSpurThickening.embedding Delta j hlen).dartWord_map]
    exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map (OuterSpurThickening.embedding Delta j hlen).faces,
      (OuterSpurThickening.embedding Delta j hlen).shelling s
        (OuterSpurThickening.outer_not_mem Delta H) hl⟩

theorem contiguityGeometry_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (htgt : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      H.targetArc.darts) :
    (contiguityGeometry Delta j hlen H htgt).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length (OuterSpurThickening.embedding Delta j hlen).darts
    (OuterSpurThickening.cellDarts_eq Delta j hlen H.source)

theorem contiguityGeometry_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (htgt : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      H.targetArc.darts) :
    (contiguityGeometry Delta j hlen H htgt).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length (OuterSpurThickening.targetImage Delta j hlen H.target)
    (OuterSpurThickening.targetDarts_eq Delta j hlen H.target)

theorem contiguityGeometry_target_start {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (htgt : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      H.targetArc.darts) :
    (contiguityGeometry Delta j hlen H htgt).targetArc.start.val = H.targetArc.start.val :=
  H.targetArc.mapTo_start (OuterSpurThickening.targetImage Delta j hlen H.target)
    (OuterSpurThickening.targetDarts_eq Delta j hlen H.target)

theorem contiguityGeometry_injective {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} {H K : ContiguityGeometry D eps Delta s}
    (hH : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      H.targetArc.darts)
    (hK : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      K.targetArc.darts)
    (h : contiguityGeometry Delta j hlen H hH = contiguityGeometry Delta j hlen K hK) :
    H = K := by
  apply ContiguityGeometry.eq_of_data
  · exact (List.map_injective_iff.mpr (OuterSpurThickening.embedding Delta j hlen).darts.injective)
      (congrArg (fun J => J.boundary.cycle) h)
  · exact (OuterSpurThickening.cellMap Delta j hlen).indexEquiv.injective
      (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr (OuterSpurThickening.cellMap Delta j hlen).indexEquiv).injective
      (congrArg (fun J => J.target) h)
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguityGeometry_source_length] using congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguityGeometry, CyclicArc.mapTo_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguityGeometry_target_length] using congrArg (fun J => J.targetArc.length) h
  · exact (List.map_injective_iff.mpr (OuterSpurThickening.embedding Delta j hlen).darts.injective)
      (congrArg (fun J => J.rightSide) h)
  · exact (List.map_injective_iff.mpr (OuterSpurThickening.embedding Delta j hlen).darts.injective)
      (congrArg (fun J => J.leftSide) h)

/-- The regions an outer doubling transports: those whose target arc does not use `alpha w_j`. -/
abbrev Transportable (D : RelGenSet G Lambda) (eps : ℕ) :=
  { a : RegionCandidate D eps Delta //
    Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts }

noncomputable def regionCandidate {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Transportable Delta j D eps) : RegionCandidate D eps (OuterSpurThickening.diagram Delta j hlen) :=
  ⟨(OuterSpurThickening.embedding Delta j hlen).faceSet a.val.1,
    contiguityGeometry Delta j hlen a.val.2 a.property⟩

theorem regionCandidate_injective {D : RelGenSet G Lambda} {eps : ℕ} :
    Function.Injective (regionCandidate Delta j hlen :
      Transportable Delta j D eps → RegionCandidate D eps (OuterSpurThickening.diagram Delta j hlen)) := by
  rintro ⟨⟨s, H⟩, hs⟩ ⟨⟨t, K⟩, ht⟩ h
  have hfaces : (OuterSpurThickening.embedding Delta j hlen).faceSet s =
      (OuterSpurThickening.embedding Delta j hlen).faceSet t :=
    congrArg Sigma.fst h
  have hst : s = t := Finset.map_injective (OuterSpurThickening.embedding Delta j hlen).faces hfaces
  subst hst
  have hcont : contiguityGeometry Delta j hlen H hs = contiguityGeometry Delta j hlen K ht :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hHK := contiguityGeometry_injective Delta j hlen hs ht hcont
  cases hHK
  rfl

theorem regionCandidate_weight {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Transportable Delta j D eps) :
    RegionCandidate.weight (regionCandidate Delta j hlen a) = RegionCandidate.weight a.val :=
  congrArg₂ Nat.add (contiguityGeometry_source_length Delta j hlen a.val.2 a.property)
    (contiguityGeometry_target_length Delta j hlen a.val.2 a.property)

theorem regionCandidate_compatible {D : RelGenSet G Lambda} {eps : ℕ}
    (a b : Transportable Delta j D eps) :
    RegionCandidate.Compatible (regionCandidate Delta j hlen a)
        (regionCandidate Delta j hlen b) ↔ RegionCandidate.Compatible a.val b.val :=
  (OuterSpurThickening.embedding Delta j hlen).faceSet_disjoint_iff a.val.1 b.val.1

theorem regionCandidate_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Transportable Delta j D eps) :
    RegionCandidate.SameTargetProfile (regionCandidate Delta j hlen a) a.val :=
  And.intro Option.map_eq_none_iff
    (And.intro (contiguityGeometry_target_start Delta j hlen a.val.2 a.property)
      (And.intro (contiguityGeometry_target_length Delta j hlen a.val.2 a.property)
        (contiguityGeometry_source_length Delta j hlen a.val.2 a.property)))

/-- The sides of a transported region are the images of the old sides. -/
theorem regionCandidate_sides {D : RelGenSet G Lambda} {eps : ℕ}
    (a : Transportable Delta j D eps) :
    (regionCandidate Delta j hlen a).2.rightSide ++ (regionCandidate Delta j hlen a).2.leftSide =
      (a.val.2.rightSide ++ a.val.2.leftSide).map (embed Delta.toCombMap) := by
  rw [List.map_append]
  rfl

noncomputable def regionFamilyEmbedding {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts) :
    family ↪ RegionCandidate D eps (OuterSpurThickening.diagram Delta j hlen) where
  toFun a := regionCandidate Delta j hlen ⟨a.val, htgt a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : Transportable Delta j D eps => x.val)
      (regionCandidate_injective Delta j hlen h)

/-- **A family whose target arcs do not use `alpha w_j`, after the doubling.** -/
noncomputable def regionFamily {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts) :
    Finset (RegionCandidate D eps (OuterSpurThickening.diagram Delta j hlen)) :=
  family.attach.map (regionFamilyEmbedding Delta j hlen family htgt)

variable {Delta j hlen} in
theorem mem_regionFamily {D : RelGenSet G Lambda} {eps : ℕ}
    {family : Finset (RegionCandidate D eps Delta)}
    {htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts}
    {a : RegionCandidate D eps (OuterSpurThickening.diagram Delta j hlen)}
    (ha : a ∈ regionFamily Delta j hlen family htgt) :
    ∃ b : family, regionCandidate Delta j hlen ⟨b.val, htgt b.val b.property⟩ = a := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b, rfl⟩

theorem regionFamily_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts)
    {a : RegionCandidate D eps (OuterSpurThickening.diagram Delta j hlen)}
    (ha : a ∈ regionFamily Delta j hlen family htgt) :
    ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  obtain ⟨b, rfl⟩ := mem_regionFamily ha
  exact ⟨b.val, b.property, regionCandidate_profile Delta j hlen _⟩

theorem regionFamily_noLoop {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts)
    (hfamily : ∀ b ∈ family, b.2.target ≠ some b.2.source)
    {a : RegionCandidate D eps (OuterSpurThickening.diagram Delta j hlen)}
    (ha : a ∈ regionFamily Delta j hlen family htgt) :
    a.2.target ≠ some a.2.source := by
  obtain ⟨b, rfl⟩ := mem_regionFamily ha
  intro h
  change Option.map (OuterSpurThickening.cellMap Delta j hlen).indexEquiv b.val.2.target =
    some ((OuterSpurThickening.cellMap Delta j hlen).indexEquiv b.val.2.source) at h
  exact hfamily b.val b.property
    (Option.map_injective (OuterSpurThickening.cellMap Delta j hlen).indexEquiv.injective h)

theorem regionFamily_card {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts) :
    (regionFamily Delta j hlen family htgt).card = family.card := by
  simp only [regionFamily, Finset.card_map, Finset.card_attach]

theorem regionFamily_weight {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts) :
    EstimatingSelection.familyWeight RegionCandidate.weight
        (regionFamily Delta j hlen family htgt) =
      EstimatingSelection.familyWeight RegionCandidate.weight family := by
  unfold EstimatingSelection.familyWeight regionFamily
  rw [Finset.sum_map]
  trans ∑ a ∈ family.attach, RegionCandidate.weight a.val
  · apply Finset.sum_congr rfl
    intro a _
    exact regionCandidate_weight Delta j hlen ⟨a.val, htgt a.val a.property⟩
  · exact Finset.sum_attach _ _

theorem regionFamily_pairwise {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (regionFamily Delta j hlen family htgt) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (regionCandidate_compatible Delta j hlen
    ⟨a.val, htgt a.val a.property⟩ ⟨b.val, htgt b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (regionFamilyEmbedding Delta j hlen family htgt) (Subtype.ext hab))

/-- The old regions correspond to the transported ones. -/
noncomputable def regionFamilyEquiv {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts) :
    family ≃ regionFamily Delta j hlen family htgt :=
  Equiv.ofBijective (fun a => ⟨regionFamilyEmbedding Delta j hlen family htgt a,
      Finset.mem_map_of_mem _ (Finset.mem_attach family a)⟩)
    (And.intro (fun a b h => (regionFamilyEmbedding Delta j hlen family htgt).injective
        (congrArg Subtype.val h))
      (fun x => by
        obtain ⟨a, _, ha⟩ := Finset.mem_map.mp x.property
        exact ⟨a, Subtype.ext ha⟩))

theorem regionFamilyEquiv_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts)
    (a : family) :
    RegionCandidate.SameTargetProfile (regionFamilyEquiv Delta j hlen family htgt a).1 a.1 :=
  regionCandidate_profile Delta j hlen ⟨a.val, htgt a.val a.property⟩

theorem regionFamilyEquiv_source {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (htgt : ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts)
    (a : family) :
    (regionFamilyEquiv Delta j hlen family htgt a).1.2.source.val = a.1.2.source.val :=
  rfl

/-- The old hypothesis gives the new one. -/
theorem not_mem_targetArc_of_avoid {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1) :
    ∀ a ∈ family,
      Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉ a.2.targetArc.darts :=
  fun a ha => OuterSpurThickening.alpha_dart_not_mem_targetArc Delta j a.2 (havoid a ha)

/-- **A side dart is not in the target arc of its own region.**  The boundary cycle lists the
source arc, the right side, the target arc and the left side without repetition. -/
theorem alpha_dart_not_mem_targetArc_of_side {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (hside : Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∈
      H.rightSide ++ H.leftSide) :
    Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j) ∉
      H.targetArc.darts := by
  intro hmem
  have hnodup := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at hnodup
  rcases FaceEdgeDoubling.mem_targetBoundaryDarts_of_mem Delta H.target H.targetArc hmem with
    h | h
  · obtain ⟨h1, -, h12⟩ := List.nodup_append.mp hnodup
    obtain ⟨-, -, h23⟩ := List.nodup_append.mp h1
    rcases List.mem_append.mp hside with hr | hl
    · exact h23 _ (List.mem_append_right _ hr) _ h rfl
    · exact h12 _ (List.mem_append_right _ h) _ hl rfl
  · rw [Delta.toCombMap.alpha_involutive (FaceEdgeDoubling.dart Delta Delta.outerFace j)] at h
    have hcycle : FaceEdgeDoubling.dart Delta Delta.outerFace j ∈ H.boundary.cycle := by
      rw [H.boundary_decomposition]
      exact List.mem_append_left _ (List.mem_append_right _ h)
    have hin := ((H.boundary.cycle_mem_iff _).mp hcycle).1
    rw [FaceEdgeDoubling.dart_face] at hin
    exact OuterSpurThickening.outer_not_mem Delta H hin

end Transport

end GroupApproximation.GGT.VanKampen.OuterDoublingTransport

#audit_axioms GroupApproximation.GGT.VanKampen.OuterDoublingTransport.contiguityGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.OuterDoublingTransport.regionCandidate_sides
#audit_axioms GroupApproximation.GGT.VanKampen.OuterDoublingTransport.regionFamily_weight
#audit_axioms GroupApproximation.GGT.VanKampen.OuterDoublingTransport.regionFamily_pairwise
#audit_axioms GroupApproximation.GGT.VanKampen.OuterDoublingTransport.regionFamilyEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.OuterDoublingTransport.not_mem_targetArc_of_avoid
#audit_axioms GroupApproximation.GGT.VanKampen.OuterDoublingTransport.alpha_dart_not_mem_targetArc_of_side
