import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.Collapsed
import GroupApproximation.GGT.VanKampen.SurgeryCellHairThickening
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Opening a cell hair preserves a clean two-gon: the transport of the family

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellHairStepStatement`.

Notation. `M := S.diagram.toCombMap`, `f` an inner face, `w := FaceEdgeDoubling.dart S.diagram f j`
(the first corner of the boundary of `f` rebased at `j`), `b := M.facePerm w` (the second corner).
The doubled map `M'` is `EdgeInsertion.toCombMap M w b`, with darts `Option (Option M.Dart)`; old
darts enter through `embed z = some (some z)`, the new edge is `{none, some none}`.  The face `f`
splits into the digon `{none, embed w}` and the face `cellFace`, which carries the old traversal of
`f` with `some none` in the place of `w`.  By `havoid`, no region of `S` contains `f` or the face
across `w`; each old region `r` becomes `r' := regionCandidate ⟨r, havoid r hr⟩`.

Mathematical proof.

(A) Crossings.  For every region `r`, side `s` and cell side `o`,
  `crossO r' s o = (crossO r s o).map embed`.  The source arc and the target arc are mapped by dart
  maps that agree with `embed` away from `w`, and `w` lies on no arc of `r` (its face `f` and the
  face across it are not in `r`).  `alpha` commutes with `embed` definitionally, and the Boolean
  selector of `crossO false` depends only on whether the target is `none`, which is preserved.
  This gives the transport `T` of the family, with cells renumbered by `indexEquiv`.

(B) Faces.  For `z ≠ w`, `faceOf' (embed z) = faceImage (faceOf z)`; `embed w` and `none` lie on the
  digon, `some none` on `cellFace`.  A new region consists of the images `keep g` of old faces
  `g ≠ f`; neither the digon nor `cellFace` is such an image.  Hence
  `faceOf' (embed z) ∈ r'.1 ↔ faceOf z ∈ r.1`.

(C) Internal darts.  `RegionInternal family' (embed z) ↔ RegionInternal family z`, and the new darts
  `none`, `some none` are not internal.  The dart `w` and its successor `b` lie on `f`, so they are
  not internal either.  So the collapsed maps are related by `ιc : x ↦ ⟨embed x, _⟩`, which commutes
  with `alpha` and misses `some none`.

(D) The dart `w` is not a crossing: a crossing on cell side `false` lies on a face of its region,
  and `f` is in no region; a crossing on cell side `true` is `alpha` of one on cell side `false`,
  so the face across `w` would be in a region.

(E) Rotation.  In the collapsed map of `M'`, the face rotation at `embed z` (`z ≠ w`) is `some none`
  when the old rotation reaches `w`, and `embed` of the old rotation otherwise; at `some none` it is
  `embed b`, the image of the old rotation at `w`.  Also `facePerm w = b ≠ w`.  This is the bypass
  hypothesis of `phiTransportAt_of_bypass`.

(F) Naming back.  `backDart` names `some none` by `w` and `none` by `alpha w`; neither is a crossing
  by (D), so face-class paths after the step name paths before it.  A dart `x'` of `M'` on a relator
  cell face `faceImage C.face`: `none` and `embed w` lie on the digon, which is no face image; for
  `some none` the face is `cellFace = faceImage f`, so `C.face = f`, the face of `w`; for `embed z`
  with `z ≠ w`, injectivity of `faceImage` gives `faceOf z = C.face`.

(G) By `hasCleanTwoGon_of_transport`, a clean two-gon of `S` is carried to one of the new family.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

open Equiv EdgeInsertion Embedded Embedded.RegionCandidate

universe u w v

section Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace)

/-- **(B) An embedded dart is on a carried region exactly when it was on the region.** -/
theorem faceOf_embed_mem_faceSet {s : Finset X.toCombMap.Face} (hs : f ∉ s)
    (z : X.toCombMap.Dart) :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf (embed X.toCombMap z) ∈
        (FaceEdgeDoubling.embedding X f j hlen hf).faceSet s ↔ X.toCombMap.faceOf z ∈ s := by
  by_cases hz : z = FaceEdgeDoubling.dart X f j
  · rw [hz, CellHairThickening.faceOf_embed_dart X f j hlen hf, FaceEdgeDoubling.dart_face X f j]
    constructor
    · intro h
      obtain ⟨g, hg, hgF⟩ := Finset.mem_map.mp h
      exact FaceEdgeDoubling.keep_ne_digon X f j hlen
        (fun hgf => hs (by rw [← hgf]; exact hg)) hgF
    · exact fun h => absurd h hs
  · rw [CellHairThickening.faceOf_embed X f j hlen hf hz]
    by_cases hzf : X.toCombMap.faceOf z = f
    · rw [hzf, FaceEdgeDoubling.faceImage_self X f j hlen]
      constructor
      · intro h
        obtain ⟨g, hg, hgF⟩ := Finset.mem_map.mp h
        exact FaceEdgeDoubling.keep_ne_cellFace X f j hlen
          (fun hgf => hs (by rw [← hgf]; exact hg)) hgF
      · exact fun h => absurd h hs
    · rw [FaceEdgeDoubling.faceImage_of_ne X f j hlen hzf]
      exact Finset.mem_map' (FaceEdgeDoubling.embedding X f j hlen hf).faces

/-- **(C) An embedded dart is internal exactly when it was internal.** -/
theorem regionInternal_embed_iff (family : Finset (RegionCandidate D eps X))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      X.toCombMap.faceOf (X.toCombMap.alpha (FaceEdgeDoubling.dart X f j)) ∉ a.1)
    (z : X.toCombMap.Dart) :
    RegionInternal (FaceEdgeDoubling.regionFamily X f j hlen hf family havoid)
        (embed X.toCombMap z) ↔ RegionInternal family z := by
  constructor
  · rintro ⟨b, hb, h1, h2⟩
    have hb' : b ∈ family.attach.map
        (FaceEdgeDoubling.regionFamilyEmbedding X f j hlen hf family havoid) := hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hb'
    exact ⟨a.1, a.2, (faceOf_embed_mem_faceSet X f j hlen hf (havoid a.1 a.2).1 z).mp h1,
      (faceOf_embed_mem_faceSet X f j hlen hf (havoid a.1 a.2).1 (X.toCombMap.alpha z)).mp h2⟩
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨FaceEdgeDoubling.regionFamilyEmbedding X f j hlen hf family havoid ⟨a, ha⟩,
      Finset.mem_map_of_mem (FaceEdgeDoubling.regionFamilyEmbedding X f j hlen hf family havoid)
        (Finset.mem_attach family ⟨a, ha⟩),
      (faceOf_embed_mem_faceSet X f j hlen hf (havoid a ha).1 z).mpr h1,
      (faceOf_embed_mem_faceSet X f j hlen hf (havoid a ha).1 (X.toCombMap.alpha z)).mpr h2⟩

/-- The first dart of a carried source arc. -/
theorem sourceHead (a : FaceEdgeDoubling.Avoiding X f j D eps) :
    (FaceEdgeDoubling.regionCandidate X f j hlen hf a).2.sourceArc.darts.head? =
      a.val.2.sourceArc.darts.head?.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  (congrArg List.head? (FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf a.val.2.sourceArc
    (FaceEdgeDoubling.carrierImage X f j hlen hf (Embedded.cell X a.val.2.source).face)
    (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart X f j hlen hf _ hd)
    (FaceEdgeDoubling.cellDarts_eq X f j hlen hf a.val.2.source)
    (FaceEdgeDoubling.dart_not_mem_sourceArc X f j a.val.2 a.property.2))).trans List.head?_map

/-- The first dart of a carried target arc. -/
theorem targetHead (a : FaceEdgeDoubling.Avoiding X f j D eps) :
    (FaceEdgeDoubling.regionCandidate X f j hlen hf a).2.targetArc.darts.head? =
      a.val.2.targetArc.darts.head?.map (FaceEdgeDoubling.embedding X f j hlen hf).darts :=
  (congrArg List.head? (FaceEdgeDoubling.mapTo_darts_of_avoid X f j hlen hf a.val.2.targetArc
    (FaceEdgeDoubling.targetImage X f j hlen hf a.val.2.target)
    (fun _ hd => FaceEdgeDoubling.targetImage_of_ne_dart X f j hlen hf _ hd)
    (FaceEdgeDoubling.targetDarts_eq X f j hlen hf a.val.2.target)
    (FaceEdgeDoubling.dart_not_mem_targetArc X f j a.val.2 a.property.1 a.property.2))).trans
    List.head?_map

theorem cross_regionCandidate_true (a : FaceEdgeDoubling.Avoiding X f j D eps) (s : Bool) :
    cross (FaceEdgeDoubling.regionCandidate X f j hlen hf a) s true =
      (cross a.val s true).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases s with
  | false => exact targetHead X f j hlen hf a
  | true => exact sourceHead X f j hlen hf a

theorem cross_regionCandidate (a : FaceEdgeDoubling.Avoiding X f j D eps) (s o : Bool) :
    cross (FaceEdgeDoubling.regionCandidate X f j hlen hf a) s o =
      (cross a.val s o).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases o with
  | true => exact cross_regionCandidate_true X f j hlen hf a s
  | false =>
    rw [cross_false, cross_false, cross_regionCandidate_true X f j hlen hf a s]
    cases cross a.val s true with
    | none => rfl
    | some _ => rfl

/-- **(A) The crossings of a carried region are the carried crossings.** -/
theorem crossO_regionCandidate (a : FaceEdgeDoubling.Avoiding X f j D eps) (s o : Bool) :
    crossO (FaceEdgeDoubling.regionCandidate X f j hlen hf a) s o =
      (crossO a.val s o).map (FaceEdgeDoubling.embedding X f j hlen hf).darts := by
  cases s with
  | true => exact cross_regionCandidate X f j hlen hf a true o
  | false =>
    rcases Option.eq_none_or_eq_some a.val.2.target with ht | ⟨i, ht⟩
    · have ht' : (FaceEdgeDoubling.regionCandidate X f j hlen hf a).2.target = none :=
        congrArg (Option.map (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv) ht
      rw [crossO_false_of_eq_none _ ht', crossO_false_of_eq_none _ ht]
      exact cross_regionCandidate X f j hlen hf a false (!o)
    · have ht' : (FaceEdgeDoubling.regionCandidate X f j hlen hf a).2.target =
          some ((FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv i) :=
        congrArg (Option.map (FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv) ht
      rw [crossO_false_of_eq_some _ ht', crossO_false_of_eq_some _ ht]
      exact cross_regionCandidate X f j hlen hf a false o

end Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The doubling of a hair edge transports the family.** -/
noncomputable def transport (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1) :
    RegionTransport S (HairOpening.sectionFamily S f j hlen hf havoid) where
  map := FaceEdgeDoubling.regionFamilyEmbedding S.diagram f j hlen hf S.family havoid
  family_eq := rfl
  cellIndex := (FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv
  source _ := rfl
  target _ := rfl
  profile a := FaceEdgeDoubling.regionCandidate_profile S.diagram f j hlen hf ⟨a.1, havoid a.1 a.2⟩
  darts := (FaceEdgeDoubling.embedding S.diagram f j hlen hf).darts
  cross a s o := crossO_regionCandidate S.diagram f j hlen hf ⟨a.1, havoid a.1 a.2⟩ s o

theorem transport_darts (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
      (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1)
    (z : S.diagram.toCombMap.Dart) :
    (transport S f j hlen hf havoid).darts z = embed S.diagram.toCombMap z :=
  rfl

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.faceOf_embed_mem_faceSet
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.regionInternal_embed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.sourceHead
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.targetHead
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.cross_regionCandidate_true
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.cross_regionCandidate
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.crossO_regionCandidate
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.transport
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.transport_darts
