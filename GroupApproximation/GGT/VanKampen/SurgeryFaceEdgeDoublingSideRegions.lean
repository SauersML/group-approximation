import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingRegions
import GroupApproximation.Meta.AxiomGuard

/-!
# Region families through the doubling of an edge across a side

`FaceEdgeDoubling.diagram` inserts a digon inside an inner face `f` along a dart `w_j`.
`SurgeryFaceEdgeDoublingRegions.lean` carries a region through the doubling when it avoids `f`
and the face across `w_j`.  Both hypotheses are used only to show that `w_j` lies in neither
contiguity arc of the region (`dart_not_mem_sourceArc`, `dart_not_mem_targetArc`).  A region
whose side runs along `f` holds the face across `w_j`, so that transport does not apply to it.
This file carries every region avoiding `f` whose arcs avoid `w_j`, with the same fields.

* `contiguityGeometryOfArcs`: the contiguity geometry through the doubling, under
  `f ∉ s` and "`w_j` lies in neither arc".
* `dart_not_mem_sourceArc_of_side`, `dart_not_mem_targetArc_of_side`: a region holding `α w_j`
  as a left or right side dart uses `w_j` in neither arc, since otherwise `α w_j` would occur
  twice in its boundary cycle.
* `dart_not_mem_sourceArc_of_not_mem_cycle`, `dart_not_mem_targetArc_of_not_mem_cycle`: the
  same for a region avoiding `f` whose boundary cycle does not hold `α w_j`.
* `familyArcAvoid_of_side`: in a family of disjoint regions avoiding `f`, where `α w_j` is a
  side dart of one region, every region uses `w_j` in neither arc.
* `regionFamilyOfArcs` with `_card`, `_weight`, `_pairwise`, `_profile`, `_noLoop` and the
  correspondence `regionFamilyOfArcsEquiv`, as in `SurgeryFaceEdgeDoublingRegions.lean`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
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

/-! ## The doubled dart and the arcs of a region -/

/-- A region holding the reverse of `w_j` as a side dart does not use `w_j` in its source arc:
the reverse would occur twice in the boundary cycle. -/
theorem dart_not_mem_sourceArc_of_side {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (hside : Delta.toCombMap.alpha (dart Delta f j) ∈ H.rightSide ++ H.leftSide) :
    dart Delta f j ∉ H.sourceArc.darts := by
  intro hmem
  have hrev : Delta.toCombMap.alpha (dart Delta f j) ∈ H.sourceArc.reverseDarts :=
    List.mem_map.mpr ⟨dart Delta f j, List.mem_reverse.mpr hmem, rfl⟩
  have hnodup := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at hnodup
  rcases List.mem_append.mp hside with hr | hl
  · exact (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hnodup).1).1).2.2 _
      hrev _ hr rfl
  · exact (List.nodup_append.mp hnodup).2.2 _
      (List.mem_append_left _ (List.mem_append_left _ hrev)) _ hl rfl

/-- A region avoiding `f` and holding the reverse of `w_j` as a side dart does not use `w_j` in
its target arc. -/
theorem dart_not_mem_targetArc_of_side {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s) (hs : f ∉ s)
    (hside : Delta.toCombMap.alpha (dart Delta f j) ∈ H.rightSide ++ H.leftSide) :
    dart Delta f j ∉ H.targetArc.darts := by
  intro hmem
  have hnodup := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at hnodup
  rcases mem_targetBoundaryDarts_of_mem Delta H.target H.targetArc hmem with h | h
  · have hcycle : dart Delta f j ∈ H.boundary.cycle := by
      rw [H.boundary_decomposition]
      exact List.mem_append_left _ (List.mem_append_right _ h)
    have hin := ((H.boundary.cycle_mem_iff _).mp hcycle).1
    rw [dart_face] at hin
    exact hs hin
  · rcases List.mem_append.mp hside with hr | hl
    · exact (List.nodup_append.mp (List.nodup_append.mp hnodup).1).2.2 _
        (List.mem_append_right _ hr) _ h rfl
    · exact (List.nodup_append.mp hnodup).2.2 _ (List.mem_append_right _ h) _ hl rfl

/-- A region whose boundary cycle does not hold the reverse of `w_j` does not use `w_j` in its
source arc. -/
theorem dart_not_mem_sourceArc_of_not_mem_cycle {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s)
    (hcycle : Delta.toCombMap.alpha (dart Delta f j) ∉ H.boundary.cycle) :
    dart Delta f j ∉ H.sourceArc.darts := by
  intro hmem
  apply hcycle
  rw [H.boundary_decomposition]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨dart Delta f j, List.mem_reverse.mpr hmem, rfl⟩)))

/-- A region avoiding `f` whose boundary cycle does not hold the reverse of `w_j` does not use
`w_j` in its target arc. -/
theorem dart_not_mem_targetArc_of_not_mem_cycle {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s) (hs : f ∉ s)
    (hcycle : Delta.toCombMap.alpha (dart Delta f j) ∉ H.boundary.cycle) :
    dart Delta f j ∉ H.targetArc.darts := by
  intro hmem
  have htgt : ∀ d ∈ targetBoundaryDarts Delta H.target H.targetArc, d ∈ H.boundary.cycle := by
    intro d hd
    rw [H.boundary_decomposition]
    exact List.mem_append_left _ (List.mem_append_right _ hd)
  rcases mem_targetBoundaryDarts_of_mem Delta H.target H.targetArc hmem with h | h
  · have hin := ((H.boundary.cycle_mem_iff _).mp (htgt _ h)).1
    rw [dart_face] at hin
    exact hs hin
  · exact hcycle (htgt _ h)

/-- The avoidance hypothesis of a family carried along its arcs. -/
abbrev FamilyArcAvoid {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) : Prop :=
  ∀ a ∈ family,
    f ∉ a.1 ∧ dart Delta f j ∉ a.2.sourceArc.darts ∧ dart Delta f j ∉ a.2.targetArc.darts

/-- **A family of disjoint regions avoiding `f`, one of which holds `α w_j` as a side dart,
avoids `w_j` in every arc.**  The region holding the side dart cannot use `w_j` in an arc, and
any other region holding `α w_j` in its boundary would meet it. -/
theorem familyArcAvoid_of_side {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta))
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family)
    (havoid : ∀ a ∈ family, f ∉ a.1) {z : RegionCandidate D eps Delta} (hz : z ∈ family)
    (hside : Delta.toCombMap.alpha (dart Delta f j) ∈ z.2.rightSide ++ z.2.leftSide) :
    FamilyArcAvoid Delta f j family := by
  intro a ha
  refine ⟨havoid a ha, ?_⟩
  by_cases haz : a = z
  · subst haz
    exact ⟨dart_not_mem_sourceArc_of_side Delta f j a.2 hside,
      dart_not_mem_targetArc_of_side Delta f j a.2 (havoid a ha) hside⟩
  · have hcycle : Delta.toCombMap.alpha (dart Delta f j) ∉ a.2.boundary.cycle := by
      intro hcyc
      have hza : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∈ a.1 :=
        ((a.2.boundary.cycle_mem_iff _).mp hcyc).1
      have hc : Delta.toCombMap.alpha (dart Delta f j) ∈ z.2.boundary.cycle := by
        rw [z.2.boundary_decomposition]
        rcases List.mem_append.mp hside with hr | hl
        · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))
        · exact List.mem_append_right _ hl
      have hzz : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∈ z.1 :=
        ((z.2.boundary.cycle_mem_iff _).mp hc).1
      exact Finset.disjoint_left.mp (hcompat a ha z hz haz) hza hzz
    exact ⟨dart_not_mem_sourceArc_of_not_mem_cycle Delta f j a.2 hcycle,
      dart_not_mem_targetArc_of_not_mem_cycle Delta f j a.2 (havoid a ha) hcycle⟩

/-! ## Contiguity geometry through the doubling -/

/-- **Contiguity geometry through the doubling, for a region using `w_j` in neither arc.** -/
noncomputable def contiguityGeometryOfArcs {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s) (hs : f ∉ s)
    (hsrc : dart Delta f j ∉ H.sourceArc.darts) (htgt : dart Delta f j ∉ H.targetArc.darts) :
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
        (cellDarts_eq Delta f j hlen hf H.source) hsrc,
      targetBoundaryDarts_transport Delta f j hlen hf H.target H.targetArc htgt]
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

theorem contiguityGeometryOfArcs_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s) (hs : f ∉ s)
    (hsrc : dart Delta f j ∉ H.sourceArc.darts) (htgt : dart Delta f j ∉ H.targetArc.darts) :
    (contiguityGeometryOfArcs Delta f j hlen hf H hs hsrc htgt).sourceArc.length =
      H.sourceArc.length :=
  H.sourceArc.mapTo_length (carrierImage Delta f j hlen hf (Embedded.cell Delta H.source).face)
    (cellDarts_eq Delta f j hlen hf H.source)

theorem contiguityGeometryOfArcs_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s) (hs : f ∉ s)
    (hsrc : dart Delta f j ∉ H.sourceArc.darts) (htgt : dart Delta f j ∉ H.targetArc.darts) :
    (contiguityGeometryOfArcs Delta f j hlen hf H hs hsrc htgt).targetArc.length =
      H.targetArc.length :=
  H.targetArc.mapTo_length (targetImage Delta f j hlen hf H.target)
    (targetDarts_eq Delta f j hlen hf H.target)

theorem contiguityGeometryOfArcs_target_start {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (H : ContiguityGeometry D eps Delta s) (hs : f ∉ s)
    (hsrc : dart Delta f j ∉ H.sourceArc.darts) (htgt : dart Delta f j ∉ H.targetArc.darts) :
    (contiguityGeometryOfArcs Delta f j hlen hf H hs hsrc htgt).targetArc.start.val =
      H.targetArc.start.val :=
  H.targetArc.mapTo_start (targetImage Delta f j hlen hf H.target)
    (targetDarts_eq Delta f j hlen hf H.target)

theorem contiguityGeometryOfArcs_injective {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} {H K : ContiguityGeometry D eps Delta s} (hs : f ∉ s)
    (hsrcH : dart Delta f j ∉ H.sourceArc.darts) (htgtH : dart Delta f j ∉ H.targetArc.darts)
    (hsrcK : dart Delta f j ∉ K.sourceArc.darts) (htgtK : dart Delta f j ∉ K.targetArc.darts)
    (h : contiguityGeometryOfArcs Delta f j hlen hf H hs hsrcH htgtH =
      contiguityGeometryOfArcs Delta f j hlen hf K hs hsrcK htgtK) : H = K := by
  apply ContiguityGeometry.eq_of_data
  · exact (List.map_injective_iff.mpr (embedding Delta f j hlen hf).darts.injective)
      (congrArg (fun J => J.boundary.cycle) h)
  · exact (cellMap Delta f j hlen hf).indexEquiv.injective (congrArg (fun J => J.source) h)
  · exact (Equiv.optionCongr (cellMap Delta f j hlen hf).indexEquiv).injective
      (congrArg (fun J => J.target) h)
  · simpa only [contiguityGeometryOfArcs, CyclicArc.mapTo_start] using
      congrArg (fun J => J.sourceArc.start.val) h
  · simpa only [contiguityGeometryOfArcs_source_length] using
      congrArg (fun J => J.sourceArc.length) h
  · simpa only [contiguityGeometryOfArcs, CyclicArc.mapTo_start] using
      congrArg (fun J => J.targetArc.start.val) h
  · simpa only [contiguityGeometryOfArcs_target_length] using
      congrArg (fun J => J.targetArc.length) h
  · exact (List.map_injective_iff.mpr (embedding Delta f j hlen hf).darts.injective)
      (congrArg (fun J => J.rightSide) h)
  · exact (List.map_injective_iff.mpr (embedding Delta f j hlen hf).darts.injective)
      (congrArg (fun J => J.leftSide) h)

/-! ## Regions and families -/

/-- The regions a doubling carries along their arcs: those avoiding `f` whose arcs avoid `w_j`. -/
abbrev ArcAvoiding (D : RelGenSet G Lambda) (eps : ℕ) :=
  { a : RegionCandidate D eps Delta //
    f ∉ a.1 ∧ dart Delta f j ∉ a.2.sourceArc.darts ∧ dart Delta f j ∉ a.2.targetArc.darts }

noncomputable def regionCandidateOfArcs {D : RelGenSet G Lambda} {eps : ℕ}
    (a : ArcAvoiding Delta f j D eps) : RegionCandidate D eps (diagram Delta f j hlen hf) :=
  ⟨(embedding Delta f j hlen hf).faceSet a.val.1,
    contiguityGeometryOfArcs Delta f j hlen hf a.val.2 a.property.1 a.property.2.1
      a.property.2.2⟩

theorem regionCandidateOfArcs_injective {D : RelGenSet G Lambda} {eps : ℕ} :
    Function.Injective (regionCandidateOfArcs Delta f j hlen hf :
      ArcAvoiding Delta f j D eps → RegionCandidate D eps (diagram Delta f j hlen hf)) := by
  rintro ⟨⟨s, H⟩, hs⟩ ⟨⟨t, K⟩, ht⟩ h
  have hfaces : (embedding Delta f j hlen hf).faceSet s =
      (embedding Delta f j hlen hf).faceSet t := congrArg Sigma.fst h
  have hst : s = t := Finset.map_injective (embedding Delta f j hlen hf).faces hfaces
  subst hst
  have hcont : contiguityGeometryOfArcs Delta f j hlen hf H hs.1 hs.2.1 hs.2.2 =
      contiguityGeometryOfArcs Delta f j hlen hf K ht.1 ht.2.1 ht.2.2 :=
    eq_of_heq (Sigma.mk.inj_iff.mp h).2
  have hHK := contiguityGeometryOfArcs_injective Delta f j hlen hf hs.1 hs.2.1 hs.2.2 ht.2.1
    ht.2.2 hcont
  cases hHK
  rfl

theorem regionCandidateOfArcs_weight {D : RelGenSet G Lambda} {eps : ℕ}
    (a : ArcAvoiding Delta f j D eps) :
    RegionCandidate.weight (regionCandidateOfArcs Delta f j hlen hf a) =
      RegionCandidate.weight a.val :=
  congrArg₂ Nat.add
    (contiguityGeometryOfArcs_source_length Delta f j hlen hf a.val.2 a.property.1
      a.property.2.1 a.property.2.2)
    (contiguityGeometryOfArcs_target_length Delta f j hlen hf a.val.2 a.property.1
      a.property.2.1 a.property.2.2)

theorem regionCandidateOfArcs_compatible {D : RelGenSet G Lambda} {eps : ℕ}
    (a b : ArcAvoiding Delta f j D eps) :
    RegionCandidate.Compatible (regionCandidateOfArcs Delta f j hlen hf a)
        (regionCandidateOfArcs Delta f j hlen hf b) ↔ RegionCandidate.Compatible a.val b.val :=
  (embedding Delta f j hlen hf).faceSet_disjoint_iff a.val.1 b.val.1

theorem regionCandidateOfArcs_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (a : ArcAvoiding Delta f j D eps) :
    RegionCandidate.SameTargetProfile (regionCandidateOfArcs Delta f j hlen hf a) a.val :=
  And.intro Option.map_eq_none_iff
    (And.intro (contiguityGeometryOfArcs_target_start Delta f j hlen hf a.val.2 a.property.1
        a.property.2.1 a.property.2.2)
      (And.intro (contiguityGeometryOfArcs_target_length Delta f j hlen hf a.val.2 a.property.1
          a.property.2.1 a.property.2.2)
        (contiguityGeometryOfArcs_source_length Delta f j hlen hf a.val.2 a.property.1
          a.property.2.1 a.property.2.2)))

noncomputable def regionFamilyOfArcsEmbedding {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family) :
    family ↪ RegionCandidate D eps (diagram Delta f j hlen hf) where
  toFun a := regionCandidateOfArcs Delta f j hlen hf ⟨a.val, havoid a.val a.property⟩
  inj' a b h := by
    apply Subtype.ext
    exact congrArg (fun x : ArcAvoiding Delta f j D eps => x.val)
      (regionCandidateOfArcs_injective Delta f j hlen hf h)

/-- **A family avoiding `f` whose arcs avoid `w_j`, after the doubling.** -/
noncomputable def regionFamilyOfArcs {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family) :
    Finset (RegionCandidate D eps (diagram Delta f j hlen hf)) :=
  family.attach.map (regionFamilyOfArcsEmbedding Delta f j hlen hf family havoid)

theorem regionFamilyOfArcs_faces {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family)
    {a : RegionCandidate D eps (diagram Delta f j hlen hf)}
    (ha : a ∈ regionFamilyOfArcs Delta f j hlen hf family havoid) :
    ∃ b ∈ family, a.1 = (embedding Delta f j hlen hf).faceSet b.1 := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, rfl⟩

theorem regionFamilyOfArcs_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family)
    {a : RegionCandidate D eps (diagram Delta f j hlen hf)}
    (ha : a ∈ regionFamilyOfArcs Delta f j hlen hf family havoid) :
    ∃ b ∈ family, RegionCandidate.SameTargetProfile a b := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨b.val, b.property, regionCandidateOfArcs_profile Delta f j hlen hf _⟩

/-- No region of a family carried through the doubling is a loop if none of the family is. -/
theorem regionFamilyOfArcs_noLoop {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family)
    (hfamily : ∀ b ∈ family, b.2.target ≠ some b.2.source)
    {a : RegionCandidate D eps (diagram Delta f j hlen hf)}
    (ha : a ∈ regionFamilyOfArcs Delta f j hlen hf family havoid) :
    a.2.target ≠ some a.2.source := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha
  intro h
  change Option.map (cellMap Delta f j hlen hf).indexEquiv b.val.2.target =
    some ((cellMap Delta f j hlen hf).indexEquiv b.val.2.source) at h
  exact hfamily b.val b.property
    (Option.map_injective (cellMap Delta f j hlen hf).indexEquiv.injective h)

theorem regionFamilyOfArcs_card {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family) :
    (regionFamilyOfArcs Delta f j hlen hf family havoid).card = family.card := by
  simp only [regionFamilyOfArcs, Finset.card_map, Finset.card_attach]

theorem regionFamilyOfArcs_weight {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family) :
    EstimatingSelection.familyWeight RegionCandidate.weight
        (regionFamilyOfArcs Delta f j hlen hf family havoid) =
      EstimatingSelection.familyWeight RegionCandidate.weight family := by
  unfold EstimatingSelection.familyWeight regionFamilyOfArcs
  rw [Finset.sum_map]
  trans ∑ a ∈ family.attach, RegionCandidate.weight a.val
  · apply Finset.sum_congr rfl
    intro a _
    exact regionCandidateOfArcs_weight Delta f j hlen hf ⟨a.val, havoid a.val a.property⟩
  · exact Finset.sum_attach _ _

theorem regionFamilyOfArcs_pairwise {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family)
    (hcompat : EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible family) :
    EstimatingSelection.PairwiseCompatible RegionCandidate.Compatible
      (regionFamilyOfArcs Delta f j hlen hf family havoid) := by
  intro x hx y hy hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hy
  apply (regionCandidateOfArcs_compatible Delta f j hlen hf
    ⟨a.val, havoid a.val a.property⟩ ⟨b.val, havoid b.val b.property⟩).mpr
  apply hcompat a.val a.property b.val b.property
  intro hab
  exact hne (congrArg (regionFamilyOfArcsEmbedding Delta f j hlen hf family havoid)
    (Subtype.ext hab))

/-- The old regions correspond to the transported ones. -/
noncomputable def regionFamilyOfArcsEquiv {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family) :
    family ≃ regionFamilyOfArcs Delta f j hlen hf family havoid :=
  Equiv.ofBijective (fun a => ⟨regionFamilyOfArcsEmbedding Delta f j hlen hf family havoid a,
      Finset.mem_map_of_mem _ (Finset.mem_attach family a)⟩)
    (And.intro (fun a b h => (regionFamilyOfArcsEmbedding Delta f j hlen hf family havoid).injective
        (congrArg Subtype.val h))
      (fun x => by
        obtain ⟨a, _, ha⟩ := Finset.mem_map.mp x.property
        exact ⟨a, Subtype.ext ha⟩))

theorem regionFamilyOfArcsEquiv_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family)
    (a : family) :
    RegionCandidate.SameTargetProfile
      (regionFamilyOfArcsEquiv Delta f j hlen hf family havoid a).1 a.1 :=
  regionCandidateOfArcs_profile Delta f j hlen hf ⟨a.val, havoid a.val a.property⟩

theorem regionFamilyOfArcsEquiv_source {D : RelGenSet G Lambda} {eps : ℕ}
    (family : Finset (RegionCandidate D eps Delta)) (havoid : FamilyArcAvoid Delta f j family)
    (a : family) :
    (regionFamilyOfArcsEquiv Delta f j hlen hf family havoid a).1.2.source.val =
      a.1.2.source.val :=
  rfl

end GroupApproximation.GGT.VanKampen.FaceEdgeDoubling

#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.dart_not_mem_sourceArc_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.dart_not_mem_targetArc_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.familyArcAvoid_of_side
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.contiguityGeometryOfArcs
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.contiguityGeometryOfArcs_injective
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.regionFamilyOfArcs_weight
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.regionFamilyOfArcs_pairwise
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.regionFamilyOfArcsEquiv
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.regionFamilyOfArcsEquiv_source
