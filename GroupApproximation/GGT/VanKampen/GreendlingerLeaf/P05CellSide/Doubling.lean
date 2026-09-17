import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Collapsed
import GroupApproximation.GGT.VanKampen.SurgeryCellSideThickening
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingFaces
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Thickening a relator-face edge across a region side preserves a clean two-gon: the transport

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellSideStepStatement`.

Notation. `M := S.diagram.toCombMap`, `f ≠ outerFace` a face, `w := FaceEdgeDoubling.dart S.diagram
f j` (the first corner of the boundary of `f` rebased at `j`), `b := secondCorner .. = M.facePerm w`
(the second corner).  The doubled map `M'` is `EdgeInsertion.toCombMap M w b`, with darts
`Option (Option M.Dart)`; old darts enter through `embed z = some (some z)`, the new edge is
`{none, some none}`.  The face `f` splits into the digon `{none, embed w}` and the face `cellFace`,
which carries the old traversal of `f` with `some none` in the place of `w`; every other face `g`
becomes `keep g = faceImage g`.  By `havoid : FamilyArcAvoid`, no region of `S` contains `f`, and no
source or target arc of a region contains `w`.  Each old region `r` becomes
`r' := regionCandidateOfArcs ⟨r, havoid r hr⟩`, with face set `faceSet r.1 = r.1.map keep`, arcs
carried by dart maps agreeing with `embed` away from `w`, and cells renumbered by `indexEquiv`.

Mathematical proof.

(A) Crossings.  For every region `r`, side `s` and cell side `o`,
  `crossO r' s o = (crossO r s o).map embed`.  The source arc is carried by `carrierImage`, the target
  arc by `targetImage`; both agree with `embed` away from `w`, and `w` is on neither arc of `r` by
  `havoid`, so the carried arcs are the `embed`-images (`mapTo_darts_of_avoid`), and their heads are
  the `embed`-images of the old heads.  `alpha` commutes with `embed` definitionally, and the
  Boolean selector of `crossO false` depends only on whether the target is `none`, which is
  preserved by `target' = target.map indexEquiv`.  This gives the transport `T` of the family
  (`transport`), with profile `regionCandidateOfArcs_profile`.

(B) Faces.  A face of `M'` lies in `faceSet s` exactly when it is `keep g` for some `g ∈ s`.  For an
  old dart `z` and `f ∉ s`: if `faceOf z ≠ f`, then `faceOf' (embed z) = faceImage (faceOf z) =
  keep (faceOf z)`, and by injectivity of `keep` it lies in `faceSet s` iff `faceOf z ∈ s`.  If
  `faceOf z = f`, then `faceOf z ∉ s`, and `faceOf' (embed z)` is the digon (for `z = w`) or
  `cellFace` (for `z ≠ w`), neither of which is `keep g` for `g ≠ f` (and every `g ∈ s` differs
  from `f`).  Hence `faceOf' (embed z) ∈ faceSet s ↔ faceOf z ∈ s`.

(C) Internal darts.  Every new region is `r'` for an old region `r`, and `f ∉ r.1`, so by (B)
  `RegionInternal family' (embed z) ↔ RegionInternal family z`.  The new dart `none` lies on the
  digon and `some none` on `cellFace`; by (B) neither face lies in a new region, so neither new dart
  is internal.  The darts `w` and `b = facePerm w` lie on `f`, which is in no old region, so they
  are not internal either.  Also `b ≠ w` (`facePerm_dart_ne`) and `sigma (alpha w) = b`.

(D) The dart `w` is not a crossing dart of any `E ⊆ family`.  Let `crossO r s o = some w`.
  * `o = false`: the crossing lies on a face of `r`, so `f = faceOf w ∈ r.1`, against `havoid`.
  * `o = true`, `s = true`: the crossing is the head of the source arc, so `w` is on the source arc,
    against `havoid`.
  * `o = true`, `s = false`, target `some i`: the crossing is the head of the target arc, against
    `havoid`.
  * `o = true`, `s = false`, target `none`: the crossing lies on `endFace none = outerFace`, so
    `f = faceOf w = outerFace`, against `hf`.

(E) Rotation.  The collapsed maps are the restrictions of `M` and `M'` to the non-internal darts,
  and by (C) `embed` restricts to an embedding `ιc` of them, commuting with `alpha`, whose first
  coordinate is `T.darts`, missing `some none`.  By `PhiMapTransport.facePerm_val_self` the old
  collapsed rotation at `w` is `b ≠ w`.  By `facePerm_val_of_retained`, for a kept `x ≠ w`, the new
  collapsed rotation at `ιc x` is `some none` if the old one reaches `w`, and `ιc` of the old one
  otherwise; by `facePerm_val_some_none` the new rotation at `some none` is `embed b`.  These are
  the bypass hypotheses of `phiTransportAt_of_bypass`, and `w` is not kept by (D).

(F) Naming back.  `PhiMapTransport.backDart` names `embed z` by `z`, `some none` by `w`, and `none`
  by `alpha w`; neither `w` nor `alpha w` is a crossing (by (D) and `phiKeepO_alpha`), and crossings
  correspond along `ιc` (`phiKeepO_map_iff`), so `eqvGen_backDart_of_retained` names every face-class
  path after the step by one before it.  The relator cell `i'` of the new diagram has face
  `faceImage (cell S (indexEquiv⁻¹ i')).face` (`cell_face_eq`).  If a dart `x'` of `M'` lies on it:
  `none` and `embed w` lie on the digon, which is no face image; `some none` lies on
  `cellFace = faceImage f`, so injectivity of `faceImage` gives `faceOf w = f = (cell S _).face`;
  `embed z` with `z ≠ w` lies on `faceImage (faceOf z)`, so `faceOf z = (cell S _).face`.

(G) Conclusion.  `phiTransportAt_of_bypass` gives `PhiTransportAt T a₀` for every `a₀`, and
  `hasCleanTwoGon_of_transport` carries the clean two-gon of `S` (its `ExtPhiData`, `NoLoops`,
  `NoMultipleEdges`, linked component, `IsTwoGon`, labels, no gap-holding corner and no holding cell)
  to the new family.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide

open Equiv Embedded Embedded.RegionCandidate

universe u w v

section Crossings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace)

theorem mem_faceSet_iff {s : Finset X.toCombMap.Face}
    {x : (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.Face} :
    x ∈ (FaceEdgeDoubling.embedding X f j hlen hf).faceSet s ↔
      ∃ g ∈ s, FaceEdgeDoubling.keep X f j hlen g = x :=
  Finset.mem_map

theorem mem_faceSet_of_eq {s : Finset X.toCombMap.Face}
    {x y : (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.Face}
    (h : x ∈ (FaceEdgeDoubling.embedding X f j hlen hf).faceSet s) (hxy : x = y) :
    y ∈ (FaceEdgeDoubling.embedding X f j hlen hf).faceSet s :=
  hxy ▸ h

/-- **(B) An old dart lies on a carried region face exactly when it lay on the region face.** -/
theorem faceOf_embed_mem_faceSet {s : Finset X.toCombMap.Face} (hs : f ∉ s)
    (z : X.toCombMap.Dart) :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf (EdgeInsertion.embed X.toCombMap z) ∈
        (FaceEdgeDoubling.embedding X f j hlen hf).faceSet s ↔ X.toCombMap.faceOf z ∈ s := by
  refine (mem_faceSet_iff X f j hlen hf).trans ?_
  by_cases hz : X.toCombMap.faceOf z = f
  · refine ⟨?_, fun h => (hs (hz ▸ h)).elim⟩
    rintro ⟨g, hg, hgz⟩
    have hgf : g ≠ f := fun hgf => hs (hgf ▸ hg)
    by_cases hzd : z = FaceEdgeDoubling.dart X f j
    · subst hzd
      exact (FaceEdgeDoubling.keep_ne_digon X f j hlen hgf
        (hgz.trans (FaceEdgeDoubling.faceOf_embed_dart_digon X f j hlen))).elim
    · exact (FaceEdgeDoubling.keep_ne_cellFace X f j hlen hgf
        (hgz.trans (FaceEdgeDoubling.faceOf_embed_of_face_of_ne X f j hlen hz hzd))).elim
  · have he : (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf
        (EdgeInsertion.embed X.toCombMap z) =
          FaceEdgeDoubling.keep X f j hlen (X.toCombMap.faceOf z) :=
      (FaceEdgeDoubling.faceOf_embed_of_face_ne X f j hlen hz).trans
        (FaceEdgeDoubling.faceImage_of_ne X f j hlen hz)
    exact ⟨fun ⟨g, hg, hgz⟩ => FaceEdgeDoubling.keep_injective X f j hlen (hgz.trans he) ▸ hg,
      fun h => ⟨_, h, he.symm⟩⟩

/-- The first dart of a carried source arc. -/
theorem sourceHead (a : FaceEdgeDoubling.ArcAvoiding X f j D eps) :
    (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a).2.sourceArc.darts.head? =
      a.val.2.sourceArc.darts.head?.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  (congrArg List.head? (FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf a.val.2.sourceArc
    (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X a.val.2.source).face)
    (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart X f j hlen hf _ hd)
    (FaceEdgeDoubling.cellDarts_eq X f j hlen hf a.val.2.source) a.property.2.1)).trans
    List.head?_map

/-- The first dart of a carried target arc. -/
theorem targetHead (a : FaceEdgeDoubling.ArcAvoiding X f j D eps) :
    (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a).2.targetArc.darts.head? =
      a.val.2.targetArc.darts.head?.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  (congrArg List.head? (FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf a.val.2.targetArc
    (FaceEdgeDoubling.targetImage X f j hlen hf a.val.2.target)
    (fun _ hd => FaceEdgeDoubling.targetImage_of_ne_dart X f j hlen hf _ hd)
    (FaceEdgeDoubling.targetDarts_eq X f j hlen hf a.val.2.target) a.property.2.2)).trans
    List.head?_map

theorem cross_regionCandidateOfArcs_true (a : FaceEdgeDoubling.ArcAvoiding X f j D eps)
    (s : Bool) :
    cross (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a) s true =
      (cross a.val s true).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases s with
  | false => exact targetHead X f j hlen hf a
  | true => exact sourceHead X f j hlen hf a

theorem cross_regionCandidateOfArcs (a : FaceEdgeDoubling.ArcAvoiding X f j D eps) (s o : Bool) :
    cross (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a) s o =
      (cross a.val s o).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases o with
  | true => exact cross_regionCandidateOfArcs_true X f j hlen hf a s
  | false =>
    rw [cross_false, cross_false, cross_regionCandidateOfArcs_true X f j hlen hf a s]
    cases cross a.val s true with
    | none => rfl
    | some _ => rfl

/-- **(A) The crossings of a carried region are the carried crossings.** -/
theorem crossO_regionCandidateOfArcs (a : FaceEdgeDoubling.ArcAvoiding X f j D eps)
    (s o : Bool) :
    crossO (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a) s o =
      (crossO a.val s o).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases s with
  | true => exact cross_regionCandidateOfArcs X f j hlen hf a true o
  | false =>
    rcases Option.eq_none_or_eq_some a.val.2.target with ht | ⟨i, ht⟩
    · have ht' : (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a).2.target = none :=
        congrArg (Option.map (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv) ht
      rw [crossO_false_of_eq_none _ ht', crossO_false_of_eq_none _ ht]
      exact cross_regionCandidateOfArcs X f j hlen hf a false (!o)
    · have ht' : (FaceEdgeDoubling.regionCandidateOfArcs X f j hlen hf a).2.target =
          some ((FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv i) :=
        congrArg (Option.map (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv) ht
      rw [crossO_false_of_eq_some _ ht', crossO_false_of_eq_some _ ht]
      exact cross_regionCandidateOfArcs X f j hlen hf a false o

end Crossings

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
  (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family)

/-- **The doubling of a cell-side edge transports the family.** -/
noncomputable def transport :
    RegionTransport S (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid) where
  map := FaceEdgeDoubling.regionFamilyOfArcsEmbedding S.diagram f j hlen hf S.family havoid
  family_eq := rfl
  cellIndex := (FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv
  source _ := rfl
  target _ := rfl
  profile a :=
    FaceEdgeDoubling.regionCandidateOfArcs_profile S.diagram f j hlen hf ⟨a.1, havoid a.1 a.2⟩
  darts := (FaceEdgeDoubling.embedding S.diagram f j hlen hf).darts
  cross a s o := crossO_regionCandidateOfArcs S.diagram f j hlen hf ⟨a.1, havoid a.1 a.2⟩ s o

/-- **(C) An old dart is internal after the step exactly when it was internal before it.** -/
theorem regionInternal_embed_iff (z : S.diagram.toCombMap.Dart) :
    RegionInternal (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family
        ((transport S f j hlen hf havoid).darts z) ↔ RegionInternal S.family z := by
  constructor
  · rintro ⟨b', hb', h1, h2⟩
    obtain ⟨b, rfl⟩ := (transport S f j hlen hf havoid).exists_map_eq hb'
    exact ⟨b.1, b.2,
      (faceOf_embed_mem_faceSet S.diagram f j hlen hf (havoid b.1 b.2).1 z).mp h1,
      (faceOf_embed_mem_faceSet S.diagram f j hlen hf (havoid b.1 b.2).1
        (S.diagram.toCombMap.alpha z)).mp h2⟩
  · rintro ⟨b, hb, h1, h2⟩
    exact ⟨(transport S f j hlen hf havoid).map ⟨b, hb⟩,
      (transport S f j hlen hf havoid).map_mem _,
      (faceOf_embed_mem_faceSet S.diagram f j hlen hf (havoid b hb).1 z).mpr h1,
      (faceOf_embed_mem_faceSet S.diagram f j hlen hf (havoid b hb).1
        (S.diagram.toCombMap.alpha z)).mpr h2⟩

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

include havoid in
/-- The doubled dart lies on `f`, which is in no region, hence is not internal. -/
theorem dart_not_internal : ¬ RegionInternal S.family (FaceEdgeDoubling.dart S.diagram f j) :=
  not_regionInternal_of_face_not_mem fun a ha h =>
    (havoid a ha).1 (Eq.mp (congrArg (fun y => y ∈ a.1)
      (FaceEdgeDoubling.dart_face S.diagram f j)) h)

include havoid in
/-- The corner after the doubled dart lies on `f`, hence is not internal. -/
theorem second_not_internal :
    ¬ RegionInternal S.family (EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen)) := by
  have hface : S.diagram.toCombMap.faceOf (EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen)) = f :=
    (congrArg S.diagram.toCombMap.faceOf
      (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram f j hlen)).trans
      ((S.diagram.toCombMap.faceOf_facePerm _).trans (FaceEdgeDoubling.dart_face S.diagram f j))
  exact not_regionInternal_of_face_not_mem fun a ha h =>
    (havoid a ha).1 (Eq.mp (congrArg (fun y => y ∈ a.1) hface) h)

/-- The new dart `some none` lies on `cellFace`, hence is not internal. -/
theorem someNone_not_internal :
    ¬ RegionInternal (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨b', hb', h1, -⟩
  obtain ⟨b, rfl⟩ := (transport S f j hlen hf havoid).exists_map_eq hb'
  have h' : (FaceEdgeDoubling.diagram S.diagram f j hlen hf).toCombMap.faceOf
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) ∈
        (FaceEdgeDoubling.embedding S.diagram f j hlen hf).faceSet b.1.1 := h1
  obtain ⟨g, hg, hgc⟩ := (mem_faceSet_iff S.diagram f j hlen hf).mp
    (mem_faceSet_of_eq S.diagram f j hlen hf h'
      (FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram f j hlen))
  exact FaceEdgeDoubling.keep_ne_cellFace S.diagram f j hlen
    (fun hgf => (havoid b.1 b.2).1 (hgf ▸ hg)) hgc

/-- The new dart `none` lies on the digon, hence is not internal. -/
theorem none_not_internal :
    ¬ RegionInternal (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family
      (none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨b', hb', h1, -⟩
  obtain ⟨b, rfl⟩ := (transport S f j hlen hf havoid).exists_map_eq hb'
  have h' : (FaceEdgeDoubling.diagram S.diagram f j hlen hf).toCombMap.faceOf
      (none : EdgeInsertion.Dart S.diagram.toCombMap) ∈
        (FaceEdgeDoubling.embedding S.diagram f j hlen hf).faceSet b.1.1 := h1
  obtain ⟨g, hg, hgc⟩ := (mem_faceSet_iff S.diagram f j hlen hf).mp
    (mem_faceSet_of_eq S.diagram f j hlen hf h'
      (FaceEdgeDoubling.faceOf_none_digon S.diagram f j hlen))
  exact FaceEdgeDoubling.keep_ne_digon S.diagram f j hlen
    (fun hgf => (havoid b.1 b.2).1 (hgf ▸ hg)) hgc

include hf havoid in
/-- **(D) The doubled dart is not a crossing dart.** -/
theorem not_phiKeepO_dart {E : Finset (RegionCandidate D eps S.diagram)} (hE : E ⊆ S.family)
    (x : (collapsedMap S.family).Dart) (hx : x.1 = FaceEdgeDoubling.dart S.diagram f j) :
    ¬ PhiKeepO S.family E x := by
  rintro ⟨a, ha, s, o, h⟩
  rw [hx] at h
  have hav := havoid a (hE ha)
  cases o with
  | false =>
    exact hav.1 (Eq.mp (congrArg (fun y => y ∈ a.1) (FaceEdgeDoubling.dart_face S.diagram f j))
      (faceOf_crossO_false a h))
  | true =>
    cases s with
    | true =>
      have hh : a.2.sourceArc.darts.head? = some (FaceEdgeDoubling.dart S.diagram f j) := h
      exact hav.2.1 (List.mem_of_mem_head? (Option.mem_def.mpr hh))
    | false =>
      rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨_, ht⟩
      · have hend : f = endFace S.diagram (sideCellO a false) :=
          (FaceEdgeDoubling.dart_face S.diagram f j).symm.trans (faceOf_crossO_true a h)
        have hs : sideCellO a false = none := ht
        rw [hs] at hend
        exact hf hend
      · rw [crossO_false_of_eq_some a ht] at h
        have hh : a.2.targetArc.darts.head? = some (FaceEdgeDoubling.dart S.diagram f j) := h
        exact hav.2.2 (List.mem_of_mem_head? (Option.mem_def.mpr hh))

/-- **(F) The relator cells of the new diagram have the face images of the old cell faces.** -/
theorem cell_face_eq
    (i' : Fin (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram.rCellCount) :
    (cell (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram i').face =
      FaceEdgeDoubling.faceImage S.diagram f j hlen
        (cell S.diagram ((transport S f j hlen hf havoid).cellIndex.symm i')).face :=
  (congrArg RelatorCell.face ((congrArg (cell (FaceEdgeDoubling.diagram S.diagram f j hlen hf))
    ((FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv.apply_symm_apply i').symm).trans
      ((FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexed_cell
        ((FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv.symm i')))).trans
    ((FaceEdgeDoubling.cellMap S.diagram f j hlen hf).face_eq _)

end Family

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.crossO_regionCandidateOfArcs
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.transport
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.regionInternal_embed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.not_phiKeepO_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.cell_face_eq
