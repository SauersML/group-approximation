import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.StepTransport
import GroupApproximation.GGT.VanKampen.SurgeryRegionPairThickeningCount
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingGeometry
import GroupApproximation.Meta.AxiomGuard

/-!
# Region-pair thickening: faces, internal darts and the doubled dart

Target: `GroupApproximation.GGT.VanKampen.TwoGonRegionPairStepStatement`.

Notation. `X := S.diagram`, `M := X.toCombMap`, `w := FaceEdgeDoubling.dart X f j`, a side dart of
the region `T.holder` holding the face `f ≠ outerFace`, `X' := FaceEdgeDoubling.diagram X f j hlen hf`
with old darts `embed z = some (some z)` and new darts `none`, `some none`.

Mathematical proof.

(F) Faces. Every region after the step has as faces the face images of the faces of the region it
  came from (`mem_stepMap_faces`): for the holder this is `holdingCandidate`, and the other regions
  avoid `f`, on which the face image is the kept face.  For `z ≠ w` the face of `embed z` is the face
  image of the face of `z` (`CellHairThickening.faceOf_embed`); the face image is injective, so
  `embed z` is on a new region exactly when `z` is on the old one.

(C) Internal darts. `w` is on `f` in the holder, and `α w` is on a face outside the holder
  (`Holding.faceOf_alpha_dart_not_mem_of_side`); any region holding the face of `w` is the holder
  (pairwise disjoint faces), so `w` is not internal.  After the step `embed w` and `none` lie on the
  digon, which is not a face image, and `α' (some none) = none`; so neither `embed w`, `none` nor
  `some none` is internal.  For `z` with `z ≠ w` and `α z ≠ w`, (F) gives that `embed z` is internal
  after the step exactly when `z` was before; if `z = w` or `α z = w` neither side is internal.

(D) Crossings. A crossing `crossO r s false = some w` lies on the face of `r`, so `f ∈ r` and `r` is
  the holder; but then `w` is on the reversed source arc or the target boundary darts, and a side
  dart is on neither.  A crossing `crossO r s true = some w` lies on an end face of `r`, a relator
  cell face or the outer face; the relator cell faces avoid the holder at least area, which holds
  `f`, and `f ≠ outerFace`.

(G) Cells. The new relator cells are indexed by `indexEquiv` and their faces are the face images.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

open Equiv Embedded Embedded.RegionCandidate

universe u w v

section Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ}
  (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace)

/-- **(F) An old dart other than `w` is on a carried face set exactly when it was before.** -/
theorem faceOf_embed_mem_iff {s : Finset X.toCombMap.Face}
    {s' : Finset (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.Face}
    (hs : ∀ F, F ∈ s' ↔ ∃ g ∈ s, FaceEdgeDoubling.faceImage X f j hlen g = F)
    {z : X.toCombMap.Dart} (hz : z ≠ FaceEdgeDoubling.dart X f j) :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf
        (EdgeInsertion.embed X.toCombMap z) ∈ s' ↔ X.toCombMap.faceOf z ∈ s := by
  rw [hs, CellHairThickening.faceOf_embed X f j hlen hf hz]
  constructor
  · rintro ⟨g, hg, hgz⟩
    rwa [← FaceEdgeDoubling.faceImage_injective X f j hlen hgz]
  · intro h
    exact ⟨_, h, rfl⟩

variable {family : Finset (RegionCandidate D eps X)}

/-- **(F) The faces of a carried region are the face images.** -/
theorem mem_stepMap_faces (T : RegionPairThickening.StepData X f j family) (a : family)
    (F : (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.Face) :
    F ∈ (RegionPairThickening.stepMap X f j hlen hf T a).val.1 ↔
      ∃ g ∈ a.val.1, FaceEdgeDoubling.faceImage X f j hlen g = F := by
  by_cases ha : a.val = T.holder
  · rw [RegionPairThickening.stepMap_val_of_eq X f j hlen hf T ha, ha]
    exact Finset.mem_map
  · rw [RegionPairThickening.stepMap_val_of_ne X f j hlen hf T ha]
    change F ∈ a.val.1.map (FaceEdgeDoubling.embedding X f j hlen hf).faces ↔ _
    rw [Finset.mem_map]
    have hnf : ∀ g ∈ a.val.1, g ≠ f := fun g hg h => (avoid_of_ne X f j T a ha).1 (h ▸ hg)
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, FaceEdgeDoubling.faceImage_of_ne X f j hlen (hnf g hg)⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, (FaceEdgeDoubling.faceImage_of_ne X f j hlen (hnf g hg)).symm⟩

end Faces

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
  (T : RegionPairThickening.StepData S.diagram f j S.family) (hlea : Delta.LeastArea)

include T in
/-- **(C) The doubled dart is not internal.** -/
theorem dart_not_internal : ¬ RegionInternal S.family (FaceEdgeDoubling.dart S.diagram f j) := by
  rintro ⟨r, hr, h1, h2⟩
  have hf1 : f ∈ r.1 := by
    rw [← FaceEdgeDoubling.dart_face S.diagram f j]
    exact h1
  have hr' : r = T.holder := eq_of_face_mem_of_face_mem S.pairwise hr T.holder_mem hf1
    (RegionPairThickening.f_mem_holder S.diagram f j T)
  exact FaceEdgeDoubling.Holding.faceOf_alpha_dart_not_mem_of_side S.diagram f j T.holder.2 T.side
    (by rw [← hr']; exact h2)

/-- **(C) The old doubled dart is not internal after the step.** -/
theorem embed_dart_not_internal :
    ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family
      (EdgeInsertion.embed S.diagram.toCombMap (FaceEdgeDoubling.dart S.diagram f j)) := by
  rintro ⟨r', hr', h1, -⟩
  obtain ⟨a, -, hfa⟩ := RegionPairThickening.mem_stepFamily_faces S.diagram f j hlen hf T hr'
  obtain ⟨g, -, hg⟩ := (hfa _).mp h1
  exact FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen g
    (hg.trans (CellHairThickening.faceOf_embed_dart S.diagram f j hlen hf))

/-- **(C) The new dart `none` lies on the digon, hence is not internal.** -/
theorem none_not_internal :
    ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family
      (none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨r', hr', h1, -⟩
  obtain ⟨a, -, hfa⟩ := RegionPairThickening.mem_stepFamily_faces S.diagram f j hlen hf T hr'
  obtain ⟨g, -, hg⟩ := (hfa _).mp h1
  exact FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen g
    (hg.trans (CellHairThickening.faceOf_none S.diagram f j hlen hf))

/-- **(C) The new dart `some none` is reversed to `none` on the digon, hence is not internal.** -/
theorem someNone_not_internal :
    ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨r', hr', -, h2⟩
  have h2' : (FaceEdgeDoubling.diagram S.diagram f j hlen hf).toCombMap.faceOf
      (none : EdgeInsertion.Dart S.diagram.toCombMap) ∈ r'.1 := h2
  obtain ⟨a, -, hfa⟩ := RegionPairThickening.mem_stepFamily_faces S.diagram f j hlen hf T hr'
  obtain ⟨g, -, hg⟩ := (hfa _).mp h2'
  exact FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen g
    (hg.trans (CellHairThickening.faceOf_none S.diagram f j hlen hf))

/-- **(C) An old dart away from `w` is internal after the step exactly when before it.** -/
theorem regionInternal_embed_iff_of_ne {z : S.diagram.toCombMap.Dart}
    (hz : z ≠ FaceEdgeDoubling.dart S.diagram f j)
    (hza : S.diagram.toCombMap.alpha z ≠ FaceEdgeDoubling.dart S.diagram f j) :
    RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family
        (EdgeInsertion.embed S.diagram.toCombMap z) ↔ RegionInternal S.family z := by
  constructor
  · rintro ⟨b', hb', h1, h2⟩
    obtain ⟨b, hb, hfb⟩ := RegionPairThickening.mem_stepFamily_faces S.diagram f j hlen hf T hb'
    exact ⟨b, hb, (faceOf_embed_mem_iff S.diagram f j hlen hf hfb hz).mp h1,
      (faceOf_embed_mem_iff S.diagram f j hlen hf hfb hza).mp h2⟩
  · rintro ⟨b, hb, h1, h2⟩
    exact ⟨(stepTransport S f j hlen hf T).map ⟨b, hb⟩,
      (stepTransport S f j hlen hf T).map_mem _,
      (faceOf_embed_mem_iff S.diagram f j hlen hf
        (mem_stepMap_faces S.diagram f j hlen hf T ⟨b, hb⟩) hz).mpr h1,
      (faceOf_embed_mem_iff S.diagram f j hlen hf
        (mem_stepMap_faces S.diagram f j hlen hf T ⟨b, hb⟩) hza).mpr h2⟩

/-- **(C) An old dart is internal after the step exactly when it was internal before it.** -/
theorem regionInternal_embed_iff (z : S.diagram.toCombMap.Dart) :
    RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family
        ((stepTransport S f j hlen hf T).darts z) ↔ RegionInternal S.family z := by
  by_cases hz : z = FaceEdgeDoubling.dart S.diagram f j
  · subst hz
    exact ⟨fun h => (embed_dart_not_internal S f j hlen hf T h).elim,
      fun h => (dart_not_internal S f j T h).elim⟩
  · by_cases hza : S.diagram.toCombMap.alpha z = FaceEdgeDoubling.dart S.diagram f j
    · constructor
      · intro h
        have h2 : RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family
            (EdgeInsertion.embed S.diagram.toCombMap (S.diagram.toCombMap.alpha z)) :=
          (regionInternal_alpha (RegionPairThickening.sectionFamily S f j hlen hf T).family
            ((stepTransport S f j hlen hf T).darts z)).mpr h
        rw [hza] at h2
        exact (embed_dart_not_internal S f j hlen hf T h2).elim
      · intro h
        exact (dart_not_internal S f j T
          (by rw [← hza]; exact (regionInternal_alpha S.family z).mpr h)).elim
    · exact regionInternal_embed_iff_of_ne S f j hlen hf T hz hza

/-- The doubled dart and the corner after it are different. -/
theorem dart_ne_second :
    FaceEdgeDoubling.dart S.diagram f j ≠
      EdgeInsertion.secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
        (FaceEdgeDoubling.second S.diagram f j hlen) :=
  fun h => FaceEdgeDoubling.Holding.facePerm_dart_ne S.diagram f j hlen
    (h.trans (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram f j hlen)).symm

/-- The corner after the doubled dart is the vertex rotation of its reverse. -/
theorem sigma_alpha_dart :
    S.diagram.toCombMap.sigma (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) =
      EdgeInsertion.secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
        (FaceEdgeDoubling.second S.diagram f j hlen) :=
  (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram f j hlen).symm

include hf T hlea in
/-- **(D) The doubled dart is not a crossing dart.** -/
theorem not_phiKeepO_dart {E : Finset (RegionCandidate D eps S.diagram)} (hE : E ⊆ S.family)
    (x : (collapsedMap S.family).Dart) (hx : x.1 = FaceEdgeDoubling.dart S.diagram f j) :
    ¬ PhiKeepO S.family E x := by
  rintro ⟨r, hr, s, o, h⟩
  rw [hx] at h
  have hleaS : S.diagram.LeastArea := S.equiv.leastArea hlea
  have hfh := RegionPairThickening.f_mem_holder S.diagram f j T
  cases o with
  | false =>
    have hfr : f ∈ r.1 := by
      rw [← FaceEdgeDoubling.dart_face S.diagram f j]
      exact faceOf_crossO_false r h
    have hr' : r = T.holder := eq_of_face_mem_of_face_mem S.pairwise (hE hr) T.holder_mem hfr hfh
    subst hr'
    rcases mem_arcs_of_crossO_false T.holder h with hm | hm
    · exact FaceEdgeDoubling.Holding.dart_not_mem_reverseDarts_of_side S.diagram f j T.holder.2
        T.side hm
    · exact FaceEdgeDoubling.Holding.dart_not_mem_targetBoundaryDarts_of_side S.diagram f j
        T.holder.2 T.side hm
  | true =>
    have hend : f = endFace S.diagram (sideCellO r s) :=
      (FaceEdgeDoubling.dart_face S.diagram f j).symm.trans (faceOf_crossO_true r h)
    cases s with
    | true =>
      have hc : f = (cell S.diagram r.2.source).face := hend
      exact (T.holder.2.innerGRegion hleaS).cells_avoid _ (cell_mem S.diagram r.2.source)
        (by rw [← hc]; exact hfh)
    | false =>
      have hend' : f = endFace S.diagram r.2.target := hend
      rcases Option.eq_none_or_eq_some r.2.target with ht | ⟨i, ht⟩
      · rw [ht] at hend'
        exact hf hend'
      · rw [ht] at hend'
        have hc : f = (cell S.diagram i).face := hend'
        exact (T.holder.2.innerGRegion hleaS).cells_avoid _ (cell_mem S.diagram i)
          (by rw [← hc]; exact hfh)

/-- **(G) The relator cells of the new diagram have the face images of the old cell faces.** -/
theorem cell_face_eq
    (i' : Fin (RegionPairThickening.sectionFamily S f j hlen hf T).diagram.rCellCount) :
    (cell (RegionPairThickening.sectionFamily S f j hlen hf T).diagram i').face =
      FaceEdgeDoubling.faceImage S.diagram f j hlen
        (cell S.diagram ((stepTransport S f j hlen hf T).cellIndex.symm i')).face :=
  congrArg RelatorCell.face ((congrArg (cell (FaceEdgeDoubling.diagram S.diagram f j hlen hf))
    ((FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv.apply_symm_apply i').symm).trans
      ((FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexed_cell
        ((FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv.symm i')))

end Family

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.faceOf_embed_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.mem_stepMap_faces
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.dart_not_internal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.embed_dart_not_internal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.none_not_internal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.someNone_not_internal
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.regionInternal_embed_iff_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.regionInternal_embed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.dart_ne_second
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.sigma_alpha_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.not_phiKeepO_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.cell_face_eq
