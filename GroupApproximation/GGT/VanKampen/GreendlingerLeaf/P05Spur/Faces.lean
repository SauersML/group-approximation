import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.Correspondence
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Outer spur thickening: faces, internal darts and the doubled dart

Target: `GroupApproximation.GGT.VanKampen.TwoGonSpurStepStatement`.

Notation as in `P05Spur/Correspondence.lean`: `M := S.diagram.toCombMap`,
`w := FaceEdgeDoubling.dart S.diagram outerFace j`, `b := secondCorner .. = M.facePerm w`, and
`M' := EdgeInsertion.toCombMap M w b` with the new darts `none`, `some none`; `hspur` says
`faceOf (alpha w) = outer`.

Mathematical proof.

(B) Faces.  A face of `M'` lies in the image `faceSet s` of a region face set `s` exactly when it
  is the face image of a face of `s`.  For an old dart `z`, `faceOf' (embed z)` is
  `faceImage (faceOf z)` when `faceOf z ≠ outer`; otherwise it is the digon (for `z = w`) or the
  new outer face `cellFace = faceImage outer` (for `z ≠ w`).  The digon is no face image, and
  `faceImage` is injective while `outer ∉ s`.  Hence `faceOf' (embed z) ∈ faceSet s ↔ faceOf z ∈ s`.

(C) Internal darts.  Every region of the new family is `faceSet` of an old region, so
  `RegionInternal family' (embed z) ↔ RegionInternal family z`.  The new darts `none` (on the
  digon) and `some none` (on `cellFace`) are not internal; neither are `w` and `b`, both on the old
  outer face, which lies in no region.

(D) The doubled dart is not a crossing dart of any set `E` of regions of `S`: `w` has the outer
  face on both sides (`dart_face` and `hspur`), and by (A') of `Correspondence` such a dart is no
  crossing.

(G) Cells.  The face of the relator cell `i'` of the new diagram is the face image of the face of
  the old relator cell `indexEquiv.symm i'`, since `cellMap` moves every cell to `spurCell`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur

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
    (OuterSpurThickening.diagram Delta j hlen).toCombMap.faceOf
        (EdgeInsertion.embed Delta.toCombMap z) ∈
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
      have hg' : g = Delta.outerFace :=
        FaceEdgeDoubling.faceImage_injective Delta Delta.outerFace j hlen
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
  (hspur : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
    (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace)

/-- **(C) An old dart is internal after the step exactly when it was internal before it.** -/
theorem regionInternal_embed_iff (z : S.diagram.toCombMap.Dart) :
    RegionInternal (OuterSpurThickening.sectionFamily S j hlen hspur).family
        ((spurTransport S j hlen hspur).darts z) ↔ RegionInternal S.family z := by
  constructor
  · rintro ⟨b', hb', h1, h2⟩
    obtain ⟨b, rfl⟩ := (spurTransport S j hlen hspur).exists_map_eq hb'
    exact ⟨b.1, b.2,
      (faceOf_embed_mem_iff S.diagram j hlen (OuterSpurThickening.outer_not_mem S.diagram b.1.2)
        z).mp h1,
      (faceOf_embed_mem_iff S.diagram j hlen (OuterSpurThickening.outer_not_mem S.diagram b.1.2)
        (S.diagram.toCombMap.alpha z)).mp h2⟩
  · rintro ⟨b, hb, h1, h2⟩
    exact ⟨(spurTransport S j hlen hspur).map ⟨b, hb⟩, (spurTransport S j hlen hspur).map_mem _,
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
      (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram S.diagram.outerFace j
        hlen)).trans
      ((S.diagram.toCombMap.faceOf_facePerm _).trans
        (FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j))
  exact not_regionInternal_of_face_not_mem fun a _ h =>
    OuterSpurThickening.outer_not_mem S.diagram a.2 (by rw [← hface]; exact h)

/-- The new dart `some none` lies on the new outer face, hence is not internal. -/
theorem someNone_not_internal :
    ¬ RegionInternal (OuterSpurThickening.sectionFamily S j hlen hspur).family
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨b', hb', h1, -⟩
  obtain ⟨b, rfl⟩ := (spurTransport S j hlen hspur).exists_map_eq hb'
  have h' : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) ∈
        (OuterSpurThickening.embedding S.diagram j hlen).faceSet b.1.1 := h1
  obtain ⟨g, hg, hgc⟩ := (mem_faceSet_iff S.diagram j hlen).mp
    (mem_faceSet_of_eq S.diagram j hlen h'
      (FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram S.diagram.outerFace j hlen))
  have hgo : g = S.diagram.outerFace :=
    FaceEdgeDoubling.faceImage_injective S.diagram S.diagram.outerFace j hlen
      (hgc.trans (FaceEdgeDoubling.faceImage_self S.diagram S.diagram.outerFace j hlen).symm)
  exact OuterSpurThickening.outer_not_mem S.diagram b.1.2 (hgo ▸ hg)

/-- The new dart `none` lies on the digon, hence is not internal. -/
theorem none_not_internal :
    ¬ RegionInternal (OuterSpurThickening.sectionFamily S j hlen hspur).family
      (none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨b', hb', h1, -⟩
  obtain ⟨b, rfl⟩ := (spurTransport S j hlen hspur).exists_map_eq hb'
  have h' : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
      (none : EdgeInsertion.Dart S.diagram.toCombMap) ∈
        (OuterSpurThickening.embedding S.diagram j hlen).faceSet b.1.1 := h1
  obtain ⟨g, -, hgc⟩ := (mem_faceSet_iff S.diagram j hlen).mp
    (mem_faceSet_of_eq S.diagram j hlen h'
      (FaceEdgeDoubling.faceOf_none_digon S.diagram S.diagram.outerFace j hlen))
  exact FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen g hgc

include hspur in
/-- **(D) The doubled dart is not a crossing dart.** -/
theorem not_phiKeepO_dart {E : Finset (RegionCandidate D eps S.diagram)}
    (x : (collapsedMap S.family).Dart)
    (hx : x.1 = FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) :
    ¬ PhiKeepO S.family E x := by
  rintro ⟨a, -, s, o, h⟩
  rw [hx] at h
  exact not_crossO_of_outer S.diagram a
    (FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j) hspur s o h

/-- **(G) The relator cells of the new diagram have the face images of the old cell faces.** -/
theorem cell_face_eq
    (i' : Fin (OuterSpurThickening.sectionFamily S j hlen hspur).diagram.rCellCount) :
    (cell (OuterSpurThickening.sectionFamily S j hlen hspur).diagram i').face =
      FaceEdgeDoubling.faceImage S.diagram S.diagram.outerFace j hlen
        (cell S.diagram ((spurTransport S j hlen hspur).cellIndex.symm i')).face :=
  congrArg RelatorCell.face ((congrArg (cell (OuterSpurThickening.diagram S.diagram j hlen))
    ((OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv.apply_symm_apply i').symm).trans
      ((OuterSpurThickening.cellMap S.diagram j hlen).indexed_cell
        ((OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv.symm i')))

end Family

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.faceOf_embed_mem_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.regionInternal_embed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.not_phiKeepO_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.cell_face_eq
