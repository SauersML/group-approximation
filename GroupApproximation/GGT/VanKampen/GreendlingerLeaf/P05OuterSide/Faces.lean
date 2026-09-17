import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.Correspondence
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Outer-side thickening: faces, internal darts and the doubled dart

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterSideStepStatement`.

Notation as in `P05OuterSide/Correspondence.lean`: `M := S.diagram.toCombMap`,
`w := FaceEdgeDoubling.dart S.diagram outerFace j`, `b := secondCorner .. = M.facePerm w`, and
`M' := EdgeInsertion.toCombMap M w b` with the new darts `none`, `some none`.

Mathematical proof.

(B) Faces. A face of `M'` lies in the image `faceSet s` of a region face set `s` exactly when it is
  the face image of a face of `s`.  For an old dart `z`, `faceOf' (embed z)` is `faceImage (faceOf z)`
  when `faceOf z ≠ outer`; otherwise it is the digon (for `z = w`) or the new outer face `cellFace`
  (for `z ≠ w`), neither of which is a face image of a face of `s`, since `outer ∉ s`.  Hence
  `faceOf' (embed z) ∈ faceSet s ↔ faceOf z ∈ s`.

(C) Internal darts. Every region of the new family is `faceSet` of an old region, so
  `RegionInternal family' (embed z) ↔ RegionInternal family z`.  The new darts `none` (on the digon)
  and `some none` (on `cellFace`) are not internal; neither are `w` and `b`, both on the old outer
  face, which lies in no region.

(D) The doubled dart is not a crossing dart of any set `E ⊆ family`: a crossing on cell side `false`
  lies on a region face; a crossing on cell side `true` lies on a relator cell face, or, for an
  unbound target, is `alpha` of the head of the target arc, and `alpha w` is not on a target arc
  by `htgt`.

(G) Cells. The face of the relator cell `i'` of the new diagram is the face image of the face of the
  old relator cell `indexEquiv.symm i'`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

open Equiv Embedded Embedded.RegionCandidate

universe u w v

section Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

theorem mem_faceSet_iff {s : Finset Delta.toCombMap.Face}
    {x : (OuterSpurThickening.diagram Delta j hlen).toCombMap.Face} :
    x ∈ (OuterSpurThickening.embedding Delta j hlen).faceSet s ↔
      ∃ g ∈ s, FaceEdgeDoubling.faceImage Delta Delta.outerFace j hlen g = x :=
  Finset.mem_map

theorem mem_faceSet_of_eq {s : Finset Delta.toCombMap.Face}
    {x y : (OuterSpurThickening.diagram Delta j hlen).toCombMap.Face}
    (h : x ∈ (OuterSpurThickening.embedding Delta j hlen).faceSet s) (hxy : x = y) :
    y ∈ (OuterSpurThickening.embedding Delta j hlen).faceSet s :=
  hxy ▸ h

/-- **(B) An old dart lies on a carried region face exactly when it lay on the region face.** -/
theorem faceOf_embed_mem_iff {s : Finset Delta.toCombMap.Face} (hs : Delta.outerFace ∉ s)
    (z : Delta.toCombMap.Dart) :
    (OuterSpurThickening.diagram Delta j hlen).toCombMap.faceOf (EdgeInsertion.embed Delta.toCombMap z) ∈
        (OuterSpurThickening.embedding Delta j hlen).faceSet s ↔
      Delta.toCombMap.faceOf z ∈ s := by
  refine (mem_faceSet_iff Delta j hlen).trans ?_
  by_cases hz : Delta.toCombMap.faceOf z = Delta.outerFace
  · refine ⟨?_, fun h => (hs (hz ▸ h)).elim⟩
    rintro ⟨g, hg, hgz⟩
    by_cases hzd : z = FaceEdgeDoubling.dart Delta Delta.outerFace j
    · subst hzd
      exact (FaceEdgeDoubling.faceImage_ne_digon Delta Delta.outerFace j hlen g
        (hgz.trans (FaceEdgeDoubling.faceOf_embed_dart_digon Delta Delta.outerFace j hlen))).elim
    · have hc := FaceEdgeDoubling.faceOf_embed_of_face_of_ne Delta Delta.outerFace j hlen hz hzd
      have hg' : g = Delta.outerFace := FaceEdgeDoubling.faceImage_injective Delta Delta.outerFace j hlen
        ((hgz.trans hc).trans (FaceEdgeDoubling.faceImage_self Delta Delta.outerFace j hlen).symm)
      exact (hs (hg' ▸ hg)).elim
  · have he := FaceEdgeDoubling.faceOf_embed_of_face_ne Delta Delta.outerFace j hlen hz
    exact ⟨fun ⟨g, hg, hgz⟩ =>
      FaceEdgeDoubling.faceImage_injective Delta Delta.outerFace j hlen (hgz.trans he) ▸ hg,
      fun h => ⟨_, h, he.symm⟩⟩

end Faces

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (htgt : ∀ a ∈ S.family, S.diagram.toCombMap.alpha
    (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) ∉ a.2.targetArc.darts)

/-- **(C) An old dart is internal after the step exactly when it was internal before it.** -/
theorem regionInternal_embed_iff (z : S.diagram.toCombMap.Dart) :
    RegionInternal (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
        ((transport S j hlen htgt).darts z) ↔ RegionInternal S.family z := by
  constructor
  · rintro ⟨b', hb', h1, h2⟩
    obtain ⟨b, rfl⟩ := (transport S j hlen htgt).exists_map_eq hb'
    exact ⟨b.1, b.2,
      (faceOf_embed_mem_iff S.diagram j hlen (OuterSpurThickening.outer_not_mem S.diagram b.1.2)
        z).mp h1,
      (faceOf_embed_mem_iff S.diagram j hlen (OuterSpurThickening.outer_not_mem S.diagram b.1.2)
        (S.diagram.toCombMap.alpha z)).mp h2⟩
  · rintro ⟨b, hb, h1, h2⟩
    exact ⟨(transport S j hlen htgt).map ⟨b, hb⟩, (transport S j hlen htgt).map_mem _,
      (faceOf_embed_mem_iff S.diagram j hlen (OuterSpurThickening.outer_not_mem S.diagram b.2)
        z).mpr h1,
      (faceOf_embed_mem_iff S.diagram j hlen (OuterSpurThickening.outer_not_mem S.diagram b.2)
        (S.diagram.toCombMap.alpha z)).mpr h2⟩

/-- The doubled dart and the corner after it are different. -/
theorem dart_ne_second :
    FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j ≠
      EdgeInsertion.secondCorner S.diagram.toCombMap
        (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
        (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen) :=
  fun h => FaceEdgeDoubling.Holding.facePerm_dart_ne S.diagram S.diagram.outerFace j hlen
    (h.trans (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram S.diagram.outerFace j
      hlen)).symm

/-- The corner after the doubled dart is the vertex rotation of its reverse. -/
theorem sigma_alpha_dart :
    S.diagram.toCombMap.sigma
        (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) =
      EdgeInsertion.secondCorner S.diagram.toCombMap
        (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
        (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen) :=
  (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram S.diagram.outerFace j hlen).symm

/-- The doubled dart lies on the outer face, hence is not internal. -/
theorem dart_not_internal :
    ¬ RegionInternal S.family (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) :=
  not_regionInternal_of_face_not_mem fun a _ h => OuterSpurThickening.outer_not_mem S.diagram a.2
    (by rw [← FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j]; exact h)

/-- The corner after the doubled dart lies on the outer face, hence is not internal. -/
theorem second_not_internal :
    ¬ RegionInternal S.family (EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen)) := by
  have hface : S.diagram.toCombMap.faceOf (EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen)) = S.diagram.outerFace :=
    (congrArg S.diagram.toCombMap.faceOf
      (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram S.diagram.outerFace j hlen)).trans
      ((S.diagram.toCombMap.faceOf_facePerm _).trans
        (FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j))
  exact not_regionInternal_of_face_not_mem fun a _ h =>
    OuterSpurThickening.outer_not_mem S.diagram a.2 (by rw [← hface]; exact h)

/-- The new dart `some none` lies on the new outer face, hence is not internal. -/
theorem someNone_not_internal :
    ¬ RegionInternal (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨b', hb', h1, -⟩
  obtain ⟨b, rfl⟩ := (transport S j hlen htgt).exists_map_eq hb'
  have h' : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) ∈
        (OuterSpurThickening.embedding S.diagram j hlen).faceSet b.1.1 := h1
  obtain ⟨g, hg, hgc⟩ := (mem_faceSet_iff S.diagram j hlen).mp (mem_faceSet_of_eq S.diagram j hlen h'
    (FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram S.diagram.outerFace j hlen))
  have hgo : g = S.diagram.outerFace :=
    FaceEdgeDoubling.faceImage_injective S.diagram S.diagram.outerFace j hlen
      (hgc.trans (FaceEdgeDoubling.faceImage_self S.diagram S.diagram.outerFace j hlen).symm)
  exact OuterSpurThickening.outer_not_mem S.diagram b.1.2 (hgo ▸ hg)

/-- The new dart `none` lies on the digon, hence is not internal. -/
theorem none_not_internal :
    ¬ RegionInternal (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
      (none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨b', hb', h1, -⟩
  obtain ⟨b, rfl⟩ := (transport S j hlen htgt).exists_map_eq hb'
  have h' : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
      (none : EdgeInsertion.Dart S.diagram.toCombMap) ∈
        (OuterSpurThickening.embedding S.diagram j hlen).faceSet b.1.1 := h1
  obtain ⟨g, -, hgc⟩ := (mem_faceSet_iff S.diagram j hlen).mp (mem_faceSet_of_eq S.diagram j hlen h'
    (FaceEdgeDoubling.faceOf_none_digon S.diagram S.diagram.outerFace j hlen))
  exact FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen g hgc

/-- **(D) The doubled dart is not a crossing dart.** -/
theorem not_phiKeepO_dart {E : Finset (RegionCandidate D eps S.diagram)} (hE : E ⊆ S.family)
    (x : (collapsedMap S.family).Dart)
    (hx : x.1 = FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) :
    ¬ PhiKeepO S.family E x := by
  rintro ⟨a, ha, s, o, h⟩
  rw [hx] at h
  have hface := FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j
  cases o with
  | false =>
    exact OuterSpurThickening.outer_not_mem S.diagram a.2
      (by rw [← hface]; exact faceOf_crossO_false a h)
  | true =>
    have hend : S.diagram.outerFace = endFace S.diagram (sideCellO a s) :=
      hface.symm.trans (faceOf_crossO_true a h)
    cases s with
    | true => exact (cell S.diagram a.2.source).face_ne_outer hend.symm
    | false =>
      rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨i, ht⟩
      · rw [crossO_false_of_eq_none a ht, Bool.not_true, cross_false, Option.map_eq_some_iff] at h
        obtain ⟨p, hp, hpa⟩ := h
        have hh : a.2.targetArc.darts.head? = some p := hp
        have hp' : p ∈ a.2.targetArc.darts := List.mem_of_mem_head? (Option.mem_def.mpr hh)
        have hpd : p = S.diagram.toCombMap.alpha
            (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) :=
          (S.diagram.toCombMap.alpha_involutive p).symm.trans
            (congrArg S.diagram.toCombMap.alpha hpa)
        exact htgt a (hE ha) (hpd ▸ hp')
      · have hend' : S.diagram.outerFace = endFace S.diagram a.2.target := hend
        rw [ht] at hend'
        exact (cell S.diagram i).face_ne_outer hend'.symm

/-- **(G) The relator cells of the new diagram have the face images of the old cell faces.** -/
theorem cell_face_eq
    (i' : Fin (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram.rCellCount) :
    (cell (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram i').face =
      FaceEdgeDoubling.faceImage S.diagram S.diagram.outerFace j hlen
        (cell S.diagram ((transport S j hlen htgt).cellIndex.symm i')).face :=
  congrArg RelatorCell.face ((congrArg (cell (OuterSpurThickening.diagram S.diagram j hlen))
    ((OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv.apply_symm_apply i').symm).trans
      ((OuterSpurThickening.cellMap S.diagram j hlen).indexed_cell
        ((OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv.symm i')))

end Family

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.faceOf_embed_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.regionInternal_embed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.not_phiKeepO_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.cell_face_eq
