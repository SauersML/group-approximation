import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# The contiguity geometry of a region holding the doubled face

`SurgeryFaceEdgeDoublingHoldingRegion.lean` carries the boundary cycle of a face set holding the
doubled face `f` through `FaceEdgeDoubling.diagram`, with the boundary dart `w_j` replaced by the
new dart.  This file carries a whole contiguity region whose **side** runs along `w_j`: the region
holding `f` in the region-pair thickening (`SurgeryRegionPairThickening.lean`).

* `faceOf_alpha_dart_not_mem_of_side`, `dart_not_mem_reverseDarts_of_side`,
  `dart_not_mem_targetBoundaryDarts_of_side`, `dart_not_mem_targetArc_of_side'`: a side dart lies on
  neither contiguity arc, and the face across it lies outside the region.
* `label_dartImage`, `dartWord_dartImage`: the new dart reads the letter of `w_j`.
* `faceOf_mem_of_shelling`, `invDarts_map_dartImage`, `shelling_dartImage`: a shelling of the region
  transports, face by face, since its walks never meet `w_j` or `α w_j` through an attaching arc.
* `holdingGeometry`: the contiguity geometry, with arcs through the dart embedding and sides through
  `dartImage`; `holdingCandidate`, with the same weight and target profile.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, "Hull's small cancellation theorem", through Osin's
Lemma 9.7(b)); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.Holding

open HullSC EdgeInsertion Surgery Embedded
open scoped Classical

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
variable (Delta : DiscDiagram.{u, w, v} W) (f : Delta.toCombMap.Face)
  (j : Fin (Delta.faceBoundary f).darts.length)
  (hlen : 1 < (Delta.faceBoundary f).darts.length) (hf : f ≠ Delta.outerFace)

/-! ## A side dart and the arcs -/

section Side

variable {D : RelGenSet G Lambda} {eps : ℕ} {s : Finset Delta.toCombMap.Face}

/-- The face across a side dart lies outside the region. -/
theorem faceOf_alpha_dart_not_mem_of_side (H : ContiguityGeometry D eps Delta s)
    (hside : dart Delta f j ∈ H.rightSide ++ H.leftSide) :
    Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s := by
  have hcyc : dart Delta f j ∈ H.boundary.cycle := by
    rw [H.boundary_decomposition]
    rcases List.mem_append.mp hside with hr | hl
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hr))
    · exact List.mem_append_right _ hl
  exact ((H.boundary.cycle_mem_iff _).mp hcyc).2

/-- A side dart is no reversed source-arc dart. -/
theorem dart_not_mem_reverseDarts_of_side (H : ContiguityGeometry D eps Delta s)
    (hside : dart Delta f j ∈ H.rightSide ++ H.leftSide) :
    dart Delta f j ∉ H.sourceArc.reverseDarts := by
  intro hrd
  have hnodup := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at hnodup
  rcases List.mem_append.mp hside with hr | hl
  · exact (List.nodup_append.mp (List.nodup_append.mp (List.nodup_append.mp hnodup).1).1).2.2 _
      hrd _ hr rfl
  · exact (List.nodup_append.mp hnodup).2.2 _
      (List.mem_append_left _ (List.mem_append_left _ hrd)) _ hl rfl

/-- A side dart is no target boundary dart. -/
theorem dart_not_mem_targetBoundaryDarts_of_side (H : ContiguityGeometry D eps Delta s)
    (hside : dart Delta f j ∈ H.rightSide ++ H.leftSide) :
    dart Delta f j ∉ targetBoundaryDarts Delta H.target H.targetArc := by
  intro htbd
  have hnodup := H.boundary.cycle_nodup
  rw [H.boundary_decomposition] at hnodup
  rcases List.mem_append.mp hside with hr | hl
  · exact (List.nodup_append.mp (List.nodup_append.mp hnodup).1).2.2 _
      (List.mem_append_right _ hr) _ htbd rfl
  · exact (List.nodup_append.mp hnodup).2.2 _ (List.mem_append_right _ htbd) _ hl rfl

/-- A side dart lies in no target arc of its region. -/
theorem dart_not_mem_targetArc_of_side' (H : ContiguityGeometry D eps Delta s)
    (hside : dart Delta f j ∈ H.rightSide ++ H.leftSide) :
    dart Delta f j ∉ H.targetArc.darts := by
  intro hmem
  rcases mem_targetBoundaryDarts_of_mem Delta H.target H.targetArc hmem with h | h
  · exact dart_not_mem_targetBoundaryDarts_of_side Delta f j H hside h
  · have hcyc : Delta.toCombMap.alpha (dart Delta f j) ∈ H.boundary.cycle := by
      rw [H.boundary_decomposition]
      exact List.mem_append_left _ (List.mem_append_right _ h)
    exact faceOf_alpha_dart_not_mem_of_side Delta f j H hside
      ((H.boundary.cycle_mem_iff _).mp hcyc).1

end Side

/-! ## Words -/

theorem label_dartImage (d : Delta.toCombMap.Dart) :
    (diagram Delta f j hlen hf).label (dartImage Delta f j hlen d) = Delta.label d := by
  by_cases hd : d = dart Delta f j
  · rw [hd, dartImage_dart]
    rfl
  · rw [dartImage_of_ne Delta f j hlen hd]
    rfl

theorem dartWord_dartImage (l : List Delta.toCombMap.Dart) :
    dartWord (diagram Delta f j hlen hf) (l.map (dartImage Delta f j hlen)) =
      dartWord Delta l := by
  simp only [dartWord, List.map_map]
  exact List.map_congr_left (fun d _ => label_dartImage Delta f j hlen hf d)

/-- Off `w_j` the dart map is the dart embedding. -/
theorem map_dartImage_of_not_mem {l : List Delta.toCombMap.Dart} (h : dart Delta f j ∉ l) :
    l.map (dartImage Delta f j hlen) = l.map (embedding Delta f j hlen hf).darts :=
  List.map_congr_left (fun _ hd => dartImage_of_ne Delta f j hlen (fun heq => h (heq ▸ hd)))

/-! ## Shelling -/

/-- Every walk of a shelling of `s` lies in `s`. -/
theorem faceOf_mem_of_shelling {s : Finset Delta.toCombMap.Face} {l : List Delta.toCombMap.Face}
    {cycle : List Delta.toCombMap.Dart} (H : FaceShelling Delta s l cycle) :
    ∀ d ∈ cycle, Delta.toCombMap.faceOf d ∈ s := by
  induction H with
  | empty =>
    intro d hd
    simp at hd
  | @step l before arc after exposed g hg k hrot rest ih =>
    intro d hd
    rcases List.mem_append.mp hd with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · exact ih d (List.mem_append_left _ (List.mem_append_left _ h1))
      · have hmem : d ∈ (Delta.faceBoundary g).darts.rotate k := by
          rw [hrot]
          exact List.mem_append_left _ h2
        rw [((Delta.faceBoundary g).mem_iff d).mp (List.mem_rotate.mp hmem)]
        exact hg
    · exact ih d (List.mem_append_right _ h3)

/-- Reversal commutes with the dart map on a list avoiding `w_j` and `α w_j`. -/
theorem invDarts_map_dartImage {l : List Delta.toCombMap.Dart}
    (hl : ∀ d ∈ l, d ≠ dart Delta f j ∧ Delta.toCombMap.alpha d ≠ dart Delta f j) :
    invDarts (diagram Delta f j hlen hf) (l.map (dartImage Delta f j hlen)) =
      (invDarts Delta l).map (dartImage Delta f j hlen) := by
  change ((l.map (dartImage Delta f j hlen)).reverse.map
      (diagram Delta f j hlen hf).toCombMap.alpha) =
    (l.reverse.map Delta.toCombMap.alpha).map (dartImage Delta f j hlen)
  exact (congrArg (List.map (diagram Delta f j hlen hf).toCombMap.alpha)
      (List.map_reverse (f := dartImage Delta f j hlen) (l := l)).symm).trans
    ((List.map_map (g := (diagram Delta f j hlen hf).toCombMap.alpha)
        (f := dartImage Delta f j hlen) (l := l.reverse)).trans
      ((List.map_congr_left fun d hd =>
          alpha_dartImage_of_ne Delta f j hlen (hl d (List.mem_reverse.mp hd)).1
            (hl d (List.mem_reverse.mp hd)).2).trans
        (List.map_map (g := dartImage Delta f j hlen) (f := Delta.toCombMap.alpha)
          (l := l.reverse)).symm))

/-- **A shelling of a face set holding `f` transports**, face by face, when the face across `w_j`
lies outside the face set. -/
theorem shelling_dartImage {s : Finset Delta.toCombMap.Face}
    (hw : Delta.toCombMap.faceOf (Delta.toCombMap.alpha (dart Delta f j)) ∉ s)
    {l : List Delta.toCombMap.Face} {cycle : List Delta.toCombMap.Dart}
    (H : FaceShelling Delta s l cycle) :
    FaceShelling (diagram Delta f j hlen hf) (holdingFaceSet Delta f j hlen hf s)
      (l.map (faceImage Delta f j hlen)) (cycle.map (dartImage Delta f j hlen)) := by
  induction H with
  | empty => exact FaceShelling.empty
  | @step l before arc after exposed g hg k hrot rest ih =>
    simp only [List.map_cons, List.map_append] at ih ⊢
    have hwalk := faceOf_mem_of_shelling Delta rest
    have harc : ∀ d ∈ arc, d ≠ dart Delta f j ∧ Delta.toCombMap.alpha d ≠ dart Delta f j := by
      intro d hd
      have hds : Delta.toCombMap.faceOf d ∈ s :=
        hwalk d (List.mem_append_left _ (List.mem_append_right _ hd))
      have hinv : Delta.toCombMap.alpha d ∈ (Delta.faceBoundary g).darts := by
        have hmem : Delta.toCombMap.alpha d ∈ (Delta.faceBoundary g).darts.rotate k := by
          rw [hrot]
          exact List.mem_append_right _ (List.mem_map.mpr ⟨d, List.mem_reverse.mpr hd, rfl⟩)
        exact List.mem_rotate.mp hmem
      refine ⟨fun heq => ?_, fun heq => ?_⟩
      · have hg' : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = g :=
          ((Delta.faceBoundary g).mem_iff _).mp hinv
        rw [heq] at hg'
        exact hw (hg' ▸ hg)
      · have hdeq : d = Delta.toCombMap.alpha (dart Delta f j) := by
          rw [← heq, Delta.toCombMap.alpha_involutive d]
        rw [hdeq] at hds
        exact hw hds
    have hgimg : ∀ d ∈ (Delta.faceBoundary g).darts,
        carrierImage Delta f j hlen hf g d = dartImage Delta f j hlen d := by
      intro d hd
      by_cases hgf : g = f
      · rw [hgf, carrierImage_self]
      · rw [carrierImage_of_ne Delta f j hlen hf hgf, dartImage_of_ne Delta f j hlen]
        intro heq
        have hface : Delta.toCombMap.faceOf d = g := ((Delta.faceBoundary g).mem_iff d).mp hd
        rw [heq, dart_face] at hface
        exact hgf hface.symm
    refine FaceShelling.step (Delta := diagram Delta f j hlen hf)
      (faces := holdingFaceSet Delta f j hlen hf s) (faceImage Delta f j hlen g)
      ((mem_holdingFaceSet_faceImage Delta f j hlen hf s g).mpr hg) k ?_ ih
    rw [boundary_faceImage_darts Delta f j hlen hf g, List.map_congr_left hgimg,
      ← List.map_rotate, hrot, List.map_append, invDarts_map_dartImage Delta f j hlen hf harc]
    rfl

/-! ## The contiguity geometry -/

section Geometry

variable {D : RelGenSet G Lambda} {eps : ℕ} {s : Finset Delta.toCombMap.Face}

/-- **The contiguity geometry of a region holding `f`, after the doubling along a side dart.**  The
arcs go through the dart embedding, the sides through `dartImage`. -/
noncomputable def holdingGeometry (H : ContiguityGeometry D eps Delta s)
    (hside : dart Delta f j ∈ H.rightSide ++ H.leftSide) :
    ContiguityGeometry D eps (diagram Delta f j hlen hf) (holdingFaceSet Delta f j hlen hf s) where
  boundary := holdingBoundary Delta f j hlen hf s
    (faceOf_alpha_dart_not_mem_of_side Delta f j H hside) H.boundary
  source := (cellMap Delta f j hlen hf).indexEquiv H.source
  target := H.target.map (cellMap Delta f j hlen hf).indexEquiv
  sourceArc := H.sourceArc.mapTo
    (carrierImage Delta f j hlen hf (Embedded.cell Delta H.source).face)
    (cellDarts_eq Delta f j hlen hf H.source)
  targetArc := H.targetArc.mapTo (targetImage Delta f j hlen hf H.target)
    (targetDarts_eq Delta f j hlen hf H.target)
  rightSide := H.rightSide.map (dartImage Delta f j hlen)
  leftSide := H.leftSide.map (dartImage Delta f j hlen)
  boundary_decomposition := by
    change H.boundary.cycle.map (dartImage Delta f j hlen) = _
    rw [reverseDarts_of_avoid Delta f j hlen hf H.sourceArc
        (carrierImage Delta f j hlen hf (Embedded.cell Delta H.source).face)
        (fun _ hd => carrierImage_of_ne_dart Delta f j hlen hf _ hd)
        (cellDarts_eq Delta f j hlen hf H.source)
        (dart_not_mem_sourceArc Delta f j H (faceOf_alpha_dart_not_mem_of_side Delta f j H hside)),
      targetBoundaryDarts_transport Delta f j hlen hf H.target H.targetArc
        (dart_not_mem_targetArc_of_side' Delta f j H hside),
      H.boundary_decomposition, List.map_append, List.map_append, List.map_append,
      map_dartImage_of_not_mem Delta f j hlen hf (dart_not_mem_reverseDarts_of_side Delta f j H hside),
      map_dartImage_of_not_mem Delta f j hlen hf
        (dart_not_mem_targetBoundaryDarts_of_side Delta f j H hside)]
    rfl
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by
    rw [dartWord_dartImage Delta f j hlen hf]
    exact H.rightSide_norm_le
  leftSide_norm_le := by
    rw [dartWord_dartImage Delta f j hlen hf]
    exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map (faceImage Delta f j hlen),
      shelling_dartImage Delta f j hlen hf (faceOf_alpha_dart_not_mem_of_side Delta f j H hside) hl⟩

theorem holdingGeometry_source_length (H : ContiguityGeometry D eps Delta s)
    (hside : dart Delta f j ∈ H.rightSide ++ H.leftSide) :
    (holdingGeometry Delta f j hlen hf H hside).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length (carrierImage Delta f j hlen hf (Embedded.cell Delta H.source).face)
    (cellDarts_eq Delta f j hlen hf H.source)

theorem holdingGeometry_target_length (H : ContiguityGeometry D eps Delta s)
    (hside : dart Delta f j ∈ H.rightSide ++ H.leftSide) :
    (holdingGeometry Delta f j hlen hf H hside).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length (targetImage Delta f j hlen hf H.target)
    (targetDarts_eq Delta f j hlen hf H.target)

theorem holdingGeometry_target_start (H : ContiguityGeometry D eps Delta s)
    (hside : dart Delta f j ∈ H.rightSide ++ H.leftSide) :
    (holdingGeometry Delta f j hlen hf H hside).targetArc.start.val = H.targetArc.start.val :=
  H.targetArc.mapTo_start (targetImage Delta f j hlen hf H.target)
    (targetDarts_eq Delta f j hlen hf H.target)

end Geometry

/-! ## The region candidate -/

/-- The region holding `f`, after the doubling along its side dart `w_j`. -/
noncomputable def holdingCandidate {D : RelGenSet G Lambda} {eps : ℕ}
    (a : RegionCandidate D eps Delta) (hside : dart Delta f j ∈ a.2.rightSide ++ a.2.leftSide) :
    RegionCandidate D eps (diagram Delta f j hlen hf) :=
  ⟨holdingFaceSet Delta f j hlen hf a.1, holdingGeometry Delta f j hlen hf a.2 hside⟩

theorem holdingCandidate_weight {D : RelGenSet G Lambda} {eps : ℕ}
    (a : RegionCandidate D eps Delta) (hside : dart Delta f j ∈ a.2.rightSide ++ a.2.leftSide) :
    RegionCandidate.weight (holdingCandidate Delta f j hlen hf a hside) =
      RegionCandidate.weight a :=
  congrArg₂ Nat.add (holdingGeometry_source_length Delta f j hlen hf a.2 hside)
    (holdingGeometry_target_length Delta f j hlen hf a.2 hside)

theorem holdingCandidate_profile {D : RelGenSet G Lambda} {eps : ℕ}
    (a : RegionCandidate D eps Delta) (hside : dart Delta f j ∈ a.2.rightSide ++ a.2.leftSide) :
    RegionCandidate.SameTargetProfile (holdingCandidate Delta f j hlen hf a hside) a :=
  And.intro Option.map_eq_none_iff
    (And.intro (holdingGeometry_target_start Delta f j hlen hf a.2 hside)
      (And.intro (holdingGeometry_target_length Delta f j hlen hf a.2 hside)
        (holdingGeometry_source_length Delta f j hlen hf a.2 hside)))

end GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.Holding

#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.Holding.shelling_dartImage
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.Holding.holdingGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.Holding.holdingCandidate_weight
#audit_axioms GroupApproximation.GGT.VanKampen.FaceEdgeDoubling.Holding.holdingCandidate_profile
