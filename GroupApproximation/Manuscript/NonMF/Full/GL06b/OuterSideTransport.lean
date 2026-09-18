import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Proof
import GroupApproximation.GGT.VanKampen.SurgeryOuterSideThickening
import GroupApproximation.GGT.VanKampen.SurgeryGeodesicCollarDouble
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through an outer side doubling: the transport of the family

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterSideStepStatement` (the outer-side step of
the two-gon clean copy, Osin arXiv:math/0411039v3, Lemma 9.7(b), feeding Lemma 4.4; infrastructure
for `thm:hull`, non_mf_groups_exist.tex ~2121).

Notation.  `M := S.diagram.toCombMap`, `o := outerFace`, `w := FaceEdgeDoubling.dart S.diagram o j`
(a dart of the exterior traversal) and `b := secondCorner .. = M.facePerm w`.  The doubled map `M'`
is the edge insertion at `w` and `b`, with the old darts entering by `embed` and the new edge
`{none, some none}`.  The exterior splits into the digon `{none, embed w}` and `cellFace`, which is
the new exterior; every old face `g` goes to `faceImage g` (`faceImage o = cellFace`).  By `htgt`,
no target arc of the family uses `alpha w`.

Mathematical proof.

(A) Crossings.  A carried region has face set `faceSet r.1`, source arc carried by `embed`, and
  target arc carried by `targetImage`, which agrees with `embed` away from `alpha w`.  As `alpha w`
  is not on the target arc, both carried arcs are the `embed`-images, so their first darts are the
  images of the old first darts.  `alpha` commutes with `embed`, and the target is renumbered by
  `indexEquiv`, which keeps `none`.  Hence `crossO r' s c = (crossO r s c).map embed`, and the
  family is transported (`outerSideTransport`).

(B) Faces.  A region never contains `o`.  For `o ∉ s` and an old dart `z`: if `faceOf z ≠ o`, then
  `faceOf' (embed z) = faceImage (faceOf z)`, and by injectivity of `faceImage` it lies in
  `faceSet s` iff `faceOf z ∈ s`; if `faceOf z = o`, then `faceOf' (embed z)` is the digon or
  `cellFace`, and neither is `faceImage g` for `g ≠ o` (while every `g ∈ s` differs from `o`).

(C) Internal darts.  By (B) an old dart is internal after the step iff it was internal before; the
  new darts lie on the digon and on `cellFace`, which are in no carried face set; `w` and `b` lie on
  `o`, which is in no region.

(D) The dart `w` is no crossing.  If `crossO r s c = some w`: for `c = false` the crossing lies on a
  face of `r`, so `o ∈ r.1`, impossible.  For `c = true` it lies on `endFace (sideCellO r s)`, which
  is a relator cell face (never `o`) unless `s = false` and the target is `none`; in that case
  `crossO r false true = (cross r false true).map alpha`, so `alpha w` is the first dart of the
  target arc, against `htgt`.

(E) Cells.  The relator cell `i'` after the step has face `faceImage (cell S (indexEquiv⁻¹ i')).face`
  (`outerSide_cell_face_eq`).  The rotation and the naming back are in `OuterSideRotation.lean`.
-/

namespace GroupApproximation.Full.GL06b

open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.Embedded
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

universe u w v

section Crossings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {eps : ℕ} (X : DiscDiagram.{u, w, v} W)
  (j : Fin (X.faceBoundary X.outerFace).darts.length)
  (hlen : 1 < (X.faceBoundary X.outerFace).darts.length)

/-- A carried face set consists of face images (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_mem_faceSet_iff {s : Finset X.toCombMap.Face}
    {x : (OuterSpurThickening.diagram X j hlen).toCombMap.Face} :
    x ∈ (OuterSpurThickening.embedding X j hlen).faceSet s ↔
      ∃ g ∈ s, FaceEdgeDoubling.faceImage X X.outerFace j hlen g = x :=
  Finset.mem_map

/-- Membership in a carried face set along an equation (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_mem_faceSet_of_eq {s : Finset X.toCombMap.Face}
    {x y : (OuterSpurThickening.diagram X j hlen).toCombMap.Face}
    (h : x ∈ (OuterSpurThickening.embedding X j hlen).faceSet s) (hxy : x = y) :
    y ∈ (OuterSpurThickening.embedding X j hlen).faceSet s :=
  hxy ▸ h

/-- **(B) An old dart lies on a carried face set exactly when it lay on the face set** (Osin
Lemma 9.7(b), outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_faceOf_embed_mem_faceSet {s : Finset X.toCombMap.Face} (hs : X.outerFace ∉ s)
    (z : X.toCombMap.Dart) :
    (OuterSpurThickening.diagram X j hlen).toCombMap.faceOf (EdgeInsertion.embed X.toCombMap z) ∈
        (OuterSpurThickening.embedding X j hlen).faceSet s ↔ X.toCombMap.faceOf z ∈ s := by
  refine (outerSide_mem_faceSet_iff X j hlen).trans ?_
  by_cases hz : X.toCombMap.faceOf z = X.outerFace
  · refine ⟨?_, fun h => (hs (hz ▸ h)).elim⟩
    rintro ⟨g, hg, hgz⟩
    have hgf : g ≠ X.outerFace := fun hgf => hs (hgf ▸ hg)
    have hkeep : FaceEdgeDoubling.keep X X.outerFace j hlen g =
        (OuterSpurThickening.diagram X j hlen).toCombMap.faceOf
          (EdgeInsertion.embed X.toCombMap z) :=
      (FaceEdgeDoubling.faceImage_of_ne X X.outerFace j hlen hgf).symm.trans hgz
    by_cases hzd : z = FaceEdgeDoubling.dart X X.outerFace j
    · subst hzd
      exact (FaceEdgeDoubling.keep_ne_digon X X.outerFace j hlen hgf
        (hkeep.trans (FaceEdgeDoubling.faceOf_embed_dart_digon X X.outerFace j hlen))).elim
    · exact (FaceEdgeDoubling.keep_ne_cellFace X X.outerFace j hlen hgf
        (hkeep.trans (FaceEdgeDoubling.faceOf_embed_of_face_of_ne X X.outerFace j hlen hz
          hzd))).elim
  · have he : (OuterSpurThickening.diagram X j hlen).toCombMap.faceOf
        (EdgeInsertion.embed X.toCombMap z) =
          FaceEdgeDoubling.faceImage X X.outerFace j hlen (X.toCombMap.faceOf z) :=
      FaceEdgeDoubling.faceOf_embed_of_face_ne X X.outerFace j hlen hz
    exact ⟨fun ⟨g, hg, hgz⟩ =>
      FaceEdgeDoubling.faceImage_injective X X.outerFace j hlen (hgz.trans he) ▸ hg,
      fun h => ⟨_, h, he.symm⟩⟩

/-- An old dart other than `w` lies on the image of its face (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_faceOf_embed_of_ne {z : X.toCombMap.Dart}
    (hzd : z ≠ FaceEdgeDoubling.dart X X.outerFace j) :
    (OuterSpurThickening.diagram X j hlen).toCombMap.faceOf (EdgeInsertion.embed X.toCombMap z) =
      FaceEdgeDoubling.faceImage X X.outerFace j hlen (X.toCombMap.faceOf z) := by
  by_cases hz : X.toCombMap.faceOf z = X.outerFace
  · exact (FaceEdgeDoubling.faceOf_embed_of_face_of_ne X X.outerFace j hlen hz hzd).trans
      ((congrArg (FaceEdgeDoubling.faceImage X X.outerFace j hlen) hz).trans
        (FaceEdgeDoubling.faceImage_self X X.outerFace j hlen)).symm
  · exact FaceEdgeDoubling.faceOf_embed_of_face_ne X X.outerFace j hlen hz

/-- The target dart map agrees with `embed` away from `alpha w` (Osin Lemma 9.7(b), outer-side
step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_targetImage_eq (t : Option (Fin X.rCellCount)) {y : X.toCombMap.Dart}
    (hy : y ≠ X.toCombMap.alpha (FaceEdgeDoubling.dart X X.outerFace j)) :
    OuterSpurThickening.targetImage X j hlen t y = (OuterSpurThickening.embedding X j hlen).darts y := by
  cases t with
  | none => exact OuterSpurThickening.outerImage_of_ne X j hlen hy
  | some _ => rfl

/-- The first dart of a carried source arc (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_sourceHead (a : OuterDoublingTransport.Transportable X j D eps) :
    (OuterDoublingTransport.regionCandidate X j hlen a).2.sourceArc.darts.head? =
      a.val.2.sourceArc.darts.head?.map (OuterSpurThickening.embedding X j hlen).darts :=
  (congrArg List.head? (Embedded.CyclicArc.mapTo_darts a.val.2.sourceArc
    (OuterSpurThickening.embedding X j hlen).darts
    (OuterSpurThickening.cellDarts_eq X j hlen a.val.2.source))).trans List.head?_map

/-- The first dart of a carried target arc (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_targetHead (a : OuterDoublingTransport.Transportable X j D eps) :
    (OuterDoublingTransport.regionCandidate X j hlen a).2.targetArc.darts.head? =
      a.val.2.targetArc.darts.head?.map (OuterSpurThickening.embedding X j hlen).darts :=
  (congrArg List.head? ((Embedded.CyclicArc.mapTo_darts a.val.2.targetArc
    (OuterSpurThickening.targetImage X j hlen a.val.2.target)
    (OuterSpurThickening.targetDarts_eq X j hlen a.val.2.target)).trans
    (List.map_congr_left fun y hy => outerSide_targetImage_eq X j hlen a.val.2.target
      fun h => a.property (Eq.mp (congrArg (fun y' => y' ∈ a.val.2.targetArc.darts) h) hy)))).trans
    List.head?_map

/-- Carried crossings at the cells (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_cross_true (a : OuterDoublingTransport.Transportable X j D eps) (s : Bool) :
    Embedded.RegionCandidate.cross (OuterDoublingTransport.regionCandidate X j hlen a) s true =
      (Embedded.RegionCandidate.cross a.val s true).map
        (OuterSpurThickening.embedding X j hlen).darts := by
  cases s with
  | false => exact outerSide_targetHead X j hlen a
  | true => exact outerSide_sourceHead X j hlen a

/-- Carried crossings (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_cross (a : OuterDoublingTransport.Transportable X j D eps) (s o : Bool) :
    Embedded.RegionCandidate.cross (OuterDoublingTransport.regionCandidate X j hlen a) s o =
      (Embedded.RegionCandidate.cross a.val s o).map
        (OuterSpurThickening.embedding X j hlen).darts := by
  cases o with
  | true => exact outerSide_cross_true X j hlen a s
  | false =>
    rw [Embedded.RegionCandidate.cross_false, Embedded.RegionCandidate.cross_false,
      outerSide_cross_true X j hlen a s]
    cases Embedded.RegionCandidate.cross a.val s true with
    | none => rfl
    | some _ => rfl

/-- **(A) The crossings of a carried region are the carried crossings** (Osin Lemma 9.7(b),
outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_crossO (a : OuterDoublingTransport.Transportable X j D eps) (s o : Bool) :
    crossO (OuterDoublingTransport.regionCandidate X j hlen a) s o =
      (crossO a.val s o).map (OuterSpurThickening.embedding X j hlen).darts := by
  cases s with
  | true => exact outerSide_cross X j hlen a true o
  | false =>
    rcases Option.eq_none_or_eq_some a.val.2.target with ht | ⟨i, ht⟩
    · have ht' : (OuterDoublingTransport.regionCandidate X j hlen a).2.target = none :=
        congrArg (Option.map (OuterSpurThickening.cellMap X j hlen).indexEquiv) ht
      rw [crossO_false_of_eq_none _ ht', crossO_false_of_eq_none _ ht]
      exact outerSide_cross X j hlen a false (!o)
    · have ht' : (OuterDoublingTransport.regionCandidate X j hlen a).2.target =
          some ((OuterSpurThickening.cellMap X j hlen).indexEquiv i) :=
        congrArg (Option.map (OuterSpurThickening.cellMap X j hlen).indexEquiv) ht
      rw [crossO_false_of_eq_some _ ht', crossO_false_of_eq_some _ ht]
      exact outerSide_cross X j hlen a false o

end Crossings

section Family

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (htgt : ∀ a ∈ S.family, S.diagram.toCombMap.alpha
    (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) ∉ a.2.targetArc.darts)

/-- **The outer side doubling transports the family** (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
noncomputable def outerSideTransport :
    GreendlingerLeaf.P05CellSide.RegionTransport S
      (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt) where
  map := OuterDoublingTransport.regionFamilyEmbedding S.diagram j hlen S.family htgt
  family_eq := rfl
  cellIndex := (OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv
  source _ := rfl
  target _ := rfl
  profile a := OuterDoublingTransport.regionCandidate_profile S.diagram j hlen ⟨a.1, htgt a.1 a.2⟩
  darts := (OuterSpurThickening.embedding S.diagram j hlen).darts
  cross a s o := outerSide_crossO S.diagram j hlen ⟨a.1, htgt a.1 a.2⟩ s o

/-- **(C) An old dart is internal after the step exactly when it was internal before** (Osin
Lemma 9.7(b), outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_regionInternal_embed_iff (z : S.diagram.toCombMap.Dart) :
    RegionInternal (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
        ((outerSideTransport S j hlen htgt).darts z) ↔ RegionInternal S.family z := by
  constructor
  · rintro ⟨b', hb', h1, h2⟩
    obtain ⟨b, rfl⟩ := (outerSideTransport S j hlen htgt).exists_map_eq hb'
    exact ⟨b.1, b.2,
      (outerSide_faceOf_embed_mem_faceSet S.diagram j hlen
        (OuterSpurThickening.outer_not_mem S.diagram b.1.2) z).mp h1,
      (outerSide_faceOf_embed_mem_faceSet S.diagram j hlen
        (OuterSpurThickening.outer_not_mem S.diagram b.1.2) (S.diagram.toCombMap.alpha z)).mp h2⟩
  · rintro ⟨b, hb, h1, h2⟩
    exact ⟨(outerSideTransport S j hlen htgt).map ⟨b, hb⟩,
      (outerSideTransport S j hlen htgt).map_mem _,
      (outerSide_faceOf_embed_mem_faceSet S.diagram j hlen
        (OuterSpurThickening.outer_not_mem S.diagram b.2) z).mpr h1,
      (outerSide_faceOf_embed_mem_faceSet S.diagram j hlen
        (OuterSpurThickening.outer_not_mem S.diagram b.2) (S.diagram.toCombMap.alpha z)).mpr h2⟩

/-- The doubled dart and the corner after it differ (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_dart_ne_second :
    FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j ≠
      EdgeInsertion.secondCorner S.diagram.toCombMap
        (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
        (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen) :=
  fun h => FaceEdgeDoubling.Holding.facePerm_dart_ne S.diagram S.diagram.outerFace j hlen
    (h.trans (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram S.diagram.outerFace j
      hlen)).symm

/-- The corner after the doubled dart is the rotation of its reverse (Osin Lemma 9.7(b),
outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_sigma_alpha_dart :
    S.diagram.toCombMap.sigma
        (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) =
      EdgeInsertion.secondCorner S.diagram.toCombMap
        (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
        (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen) :=
  (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram S.diagram.outerFace j hlen).symm

/-- The doubled dart lies on the exterior, hence is not internal (Osin Lemma 9.7(b), outer-side
step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_dart_not_internal :
    ¬ RegionInternal S.family (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) :=
  not_regionInternal_of_face_not_mem fun a _ h =>
    OuterSpurThickening.outer_not_mem S.diagram a.2 (Eq.mp (congrArg (fun y => y ∈ a.1)
      (FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j)) h)

/-- The corner after the doubled dart lies on the exterior, hence is not internal (Osin
Lemma 9.7(b), outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_second_not_internal :
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
    OuterSpurThickening.outer_not_mem S.diagram a.2 (Eq.mp (congrArg (fun y => y ∈ a.1) hface) h)

/-- The new dart `some none` lies on the new exterior, hence is not internal (Osin Lemma 9.7(b),
outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_someNone_not_internal :
    ¬ RegionInternal (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨b', hb', h1, -⟩
  obtain ⟨b, rfl⟩ := (outerSideTransport S j hlen htgt).exists_map_eq hb'
  have h' : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
      (some none : EdgeInsertion.Dart S.diagram.toCombMap) ∈
        (OuterSpurThickening.embedding S.diagram j hlen).faceSet b.1.1 := h1
  obtain ⟨g, hg, hgc⟩ := (outerSide_mem_faceSet_iff S.diagram j hlen).mp
    (outerSide_mem_faceSet_of_eq S.diagram j hlen h'
      (FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram S.diagram.outerFace j hlen))
  have hgf : g ≠ S.diagram.outerFace := fun hgf =>
    OuterSpurThickening.outer_not_mem S.diagram b.1.2 (hgf ▸ hg)
  exact FaceEdgeDoubling.keep_ne_cellFace S.diagram S.diagram.outerFace j hlen hgf
    ((FaceEdgeDoubling.faceImage_of_ne S.diagram S.diagram.outerFace j hlen hgf).symm.trans hgc)

/-- The new dart `none` lies on the digon, hence is not internal (Osin Lemma 9.7(b), outer-side
step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_none_not_internal :
    ¬ RegionInternal (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
      (none : EdgeInsertion.Dart S.diagram.toCombMap) := by
  rintro ⟨b', hb', h1, -⟩
  obtain ⟨b, rfl⟩ := (outerSideTransport S j hlen htgt).exists_map_eq hb'
  have h' : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
      (none : EdgeInsertion.Dart S.diagram.toCombMap) ∈
        (OuterSpurThickening.embedding S.diagram j hlen).faceSet b.1.1 := h1
  obtain ⟨g, -, hgc⟩ := (outerSide_mem_faceSet_iff S.diagram j hlen).mp
    (outerSide_mem_faceSet_of_eq S.diagram j hlen h'
      (FaceEdgeDoubling.faceOf_none_digon S.diagram S.diagram.outerFace j hlen))
  exact FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen g hgc

include htgt in
/-- **(D) The doubled dart is not a crossing dart** (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_not_phiKeepO_dart {E : Finset (RegionCandidate D eps S.diagram)}
    (hE : E ⊆ S.family) (x : (collapsedMap S.family).Dart)
    (hx : x.1 = FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) :
    ¬ PhiKeepO S.family E x := by
  rintro ⟨a, ha, s, o, h⟩
  rw [hx] at h
  cases o with
  | false =>
    exact OuterSpurThickening.outer_not_mem S.diagram a.2 (Eq.mp (congrArg (fun y => y ∈ a.1)
      (FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j)) (faceOf_crossO_false a h))
  | true =>
    have hend : S.diagram.outerFace = endFace S.diagram (sideCellO a s) :=
      (FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j).symm.trans
        (faceOf_crossO_true a h)
    cases s with
    | true => exact (Embedded.cell S.diagram a.2.source).face_ne_outer hend.symm
    | false =>
      rcases Option.eq_none_or_eq_some a.2.target with ht | ⟨i, ht⟩
      · have h' : Embedded.RegionCandidate.cross a false false =
            some (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) :=
          (crossO_false_of_eq_none a ht true).symm.trans h
        rw [Embedded.RegionCandidate.cross_false] at h'
        obtain ⟨d, hd, hda⟩ := Option.map_eq_some_iff.mp h'
        have hdw : S.diagram.toCombMap.alpha
            (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) = d :=
          (congrArg S.diagram.toCombMap.alpha hda).symm.trans
            (S.diagram.toCombMap.alpha_involutive d)
        have hh : a.2.targetArc.darts.head? = some d := hd
        exact htgt a (hE ha) (Eq.mp (congrArg (fun y => y ∈ a.2.targetArc.darts) hdw.symm)
          (List.mem_of_mem_head? (Option.mem_def.mpr hh)))
      · have hs : sideCellO a false = some i := ht
        rw [hs] at hend
        exact (Embedded.cell S.diagram i).face_ne_outer hend.symm

/-- **(E) The relator cells after the step have the face images of the old cell faces** (Osin
Lemma 9.7(b), outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_cell_face_eq
    (i' : Fin (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram.rCellCount) :
    (Embedded.cell (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram i').face =
      FaceEdgeDoubling.faceImage S.diagram S.diagram.outerFace j hlen
        (Embedded.cell S.diagram ((outerSideTransport S j hlen htgt).cellIndex.symm i')).face :=
  (congrArg RelatorCell.face ((congrArg (Embedded.cell (OuterSpurThickening.diagram S.diagram j hlen))
    ((OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv.apply_symm_apply i').symm).trans
      ((OuterSpurThickening.cellMap S.diagram j hlen).indexed_cell
        ((OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv.symm i')))).trans
    ((OuterSpurThickening.cellMap S.diagram j hlen).face_eq _)

end Family

end GroupApproximation.Full.GL06b

#audit_axioms GroupApproximation.Full.GL06b.outerSide_mem_faceSet_iff
#audit_axioms GroupApproximation.Full.GL06b.outerSide_faceOf_embed_mem_faceSet
#audit_axioms GroupApproximation.Full.GL06b.outerSide_faceOf_embed_of_ne
#audit_axioms GroupApproximation.Full.GL06b.outerSide_crossO
#audit_axioms GroupApproximation.Full.GL06b.outerSideTransport
#audit_axioms GroupApproximation.Full.GL06b.outerSide_regionInternal_embed_iff
#audit_axioms GroupApproximation.Full.GL06b.outerSide_someNone_not_internal
#audit_axioms GroupApproximation.Full.GL06b.outerSide_none_not_internal
#audit_axioms GroupApproximation.Full.GL06b.outerSide_not_phiKeepO_dart
#audit_axioms GroupApproximation.Full.GL06b.outerSide_cell_face_eq
