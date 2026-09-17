import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.Collapsed
import GroupApproximation.GGT.VanKampen.SurgeryOuterCellThickening
import GroupApproximation.GGT.VanKampen.SurgeryFaceEdgeDoublingHoldingRegion
import GroupApproximation.Meta.AxiomGuard

/-!
# Outer-cell thickening preserves a clean two-gon: dart correspondence

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterCellStepStatement`.

Notation. `M := S.diagram.toCombMap`, `w := FaceEdgeDoubling.dart S.diagram outerFace j` (the
first corner `w_j` of the rebased outer boundary), `b := M.facePerm w` (the second corner). The
thickened map `M'` is `EdgeInsertion.toCombMap M w b`, with darts `Option (Option M.Dart)`;
old darts enter through `embed z = some (some z)`, the new edge is `{none, some none}`.
The hypothesis `havoid` says that no region contains the face across `w`; each old region
`r ∈ S.family` becomes `r' := OuterSpurThickening.regionCandidate ⟨r, havoid r hr⟩`.

Mathematical proof.

(A) Crossings. For every region `r`, side `s` and cell side `o`:
  `crossO r' s o = (crossO r s o).map embed`. The source arc is mapped by `embed`; the target
  arc by `targetImage`, which agrees with `embed` on every dart except `alpha w`, and the target
  arc of `r` never contains `alpha w`, since its face would lie in `r` against `havoid`
  (`OuterSpurThickening.alpha_dart_not_mem_targetArc`). The Boolean selector of `crossO false`
  depends only on whether the target is `none`, preserved by `target' = target.map indexEquiv`.

(B) Faces. For `z ≠ w`, `faceOf' (embed z) = faceImage (faceOf z)`; `embed w` and `none` lie
  on the new digon, `some none` on the new outer face `cellFace`. The regions of `S'` have the
  face sets `faceImage '' r.1`; every such face is the face of an embedded old dart, so the faces
  of `none` and `some none` lie in no region.

(C) Internal darts. `RegionInternal family' (embed z) ↔ RegionInternal family z` by (B) and the
  face membership criterion of the embedding away from the outer face; the two new darts are
  not internal. Hence the collapsed maps are related by the embedding `ιc : x ↦ ⟨embed x, _⟩`,
  which commutes with `alpha` and misses `some none`.

(D) Kept darts. `w` and `alpha w` are not crossings: a crossing on cell side `false` has its face
  in the region, while `faceOf w` is the outer face (in no region) and `faceOf (alpha w)` is
  excluded by `havoid`; a crossing on cell side `true` is `alpha` of one on side `false`.
  Neither `w` nor `b` is internal, as both lie on the outer face.

(E) Rotation. In the collapsed maps, `facePerm' (ιc x) = ιc (facePerm x)` unless
  `facePerm x = w`, in which case `facePerm' (ιc x) = some none`; and
  `facePerm' (some none) = embed b = ιc (facePerm w)`; also `facePerm w = b ≠ w`
  (`PhiMapTransport.facePerm_val_of_retained`, `facePerm_val_some_none`, `facePerm_val_self`).
  `phiTransportAt_of_bypass` then carries `phiMapO`.

(F) Naming back. `backDart` names `some none` by `w` and `none` by `alpha w`, neither a crossing,
  so face-class paths are named back (`PhiMapTransport.eqvGen_backDart_of_retained`). A dart of
  `M'` on the face `faceImage C.face` of a relator cell is `embed z` with `z ≠ w` (the new darts
  and `embed w` lie on the digon or the outer face, which are not relator cell faces), and then
  `faceOf z = C.face` by injectivity of `faceImage`.

(G) Two-gon. `hasCleanTwoGon_of_transport` carries the clean two-gon along (A)-(F).
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell

open Equiv EdgeInsertion Embedded Embedded.RegionCandidate

universe u w v

section Crossings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} (Delta : DiscDiagram.{u, w, v} W)
  (j : Fin (Delta.faceBoundary Delta.outerFace).darts.length)
  (hlen : 1 < (Delta.faceBoundary Delta.outerFace).darts.length)

/-- The target dart map agrees with the dart embedding away from `alpha w_j`. -/
theorem targetImage_eq (t : Option (Fin Delta.rCellCount)) {d : Delta.toCombMap.Dart}
    (hd : d ≠ Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) :
    OuterSpurThickening.targetImage Delta j hlen t d =
      (OuterSpurThickening.embedding Delta j hlen).darts d := by
  cases t with
  | none => exact OuterSpurThickening.outerImage_of_ne Delta j hlen hd
  | some _ => rfl

/-- The first dart of a carried source arc. -/
theorem sourceHead (a : OuterSpurThickening.Avoiding Delta j D eps) :
    (OuterSpurThickening.regionCandidate Delta j hlen a).2.sourceArc.darts.head? =
      a.val.2.sourceArc.darts.head?.map (OuterSpurThickening.embedding Delta j hlen).darts :=
  (congrArg List.head? (CyclicArc.mapTo_darts a.val.2.sourceArc
    (OuterSpurThickening.embedding Delta j hlen).darts
    (OuterSpurThickening.cellDarts_eq Delta j hlen a.val.2.source))).trans List.head?_map

/-- The first dart of a carried target arc. -/
theorem targetHead (a : OuterSpurThickening.Avoiding Delta j D eps) :
    (OuterSpurThickening.regionCandidate Delta j hlen a).2.targetArc.darts.head? =
      a.val.2.targetArc.darts.head?.map (OuterSpurThickening.embedding Delta j hlen).darts := by
  have h : (OuterSpurThickening.regionCandidate Delta j hlen a).2.targetArc.darts =
      a.val.2.targetArc.darts.map (OuterSpurThickening.embedding Delta j hlen).darts :=
    (CyclicArc.mapTo_darts a.val.2.targetArc
        (OuterSpurThickening.targetImage Delta j hlen a.val.2.target)
        (OuterSpurThickening.targetDarts_eq Delta j hlen a.val.2.target)).trans
      (List.map_congr_left fun d hd =>
        targetImage_eq Delta j hlen a.val.2.target fun h =>
          OuterSpurThickening.alpha_dart_not_mem_targetArc Delta j a.val.2 a.property
            (by rw [← h]; exact hd))
  exact (congrArg List.head? h).trans List.head?_map

theorem cross_regionCandidate_true (a : OuterSpurThickening.Avoiding Delta j D eps)
    (s : Bool) :
    cross (OuterSpurThickening.regionCandidate Delta j hlen a) s true =
      (cross a.val s true).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases s with
  | false => exact targetHead Delta j hlen a
  | true => exact sourceHead Delta j hlen a

theorem cross_regionCandidate (a : OuterSpurThickening.Avoiding Delta j D eps)
    (s o : Bool) :
    cross (OuterSpurThickening.regionCandidate Delta j hlen a) s o =
      (cross a.val s o).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases o with
  | true => exact cross_regionCandidate_true Delta j hlen a s
  | false =>
    rw [cross_false, cross_false, cross_regionCandidate_true Delta j hlen a s]
    cases cross a.val s true with
    | none => rfl
    | some _ => rfl

/-- **(A) The crossings of a carried region are the carried crossings.** -/
theorem crossO_regionCandidate (a : OuterSpurThickening.Avoiding Delta j D eps)
    (s o : Bool) :
    crossO (OuterSpurThickening.regionCandidate Delta j hlen a) s o =
      (crossO a.val s o).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases s with
  | true => exact cross_regionCandidate Delta j hlen a true o
  | false =>
    rcases Option.eq_none_or_eq_some a.val.2.target with ht | ⟨i, ht⟩
    · have ht' : (OuterSpurThickening.regionCandidate Delta j hlen a).2.target = none :=
        congrArg (Option.map (OuterSpurThickening.cellMap Delta j hlen).indexEquiv) ht
      rw [crossO_false_of_eq_none _ ht', crossO_false_of_eq_none _ ht]
      exact cross_regionCandidate Delta j hlen a false (!o)
    · have ht' : (OuterSpurThickening.regionCandidate Delta j hlen a).2.target =
          some ((OuterSpurThickening.cellMap Delta j hlen).indexEquiv i) :=
        congrArg (Option.map (OuterSpurThickening.cellMap Delta j hlen).indexEquiv) ht
      rw [crossO_false_of_eq_some _ ht', crossO_false_of_eq_some _ ht]
      exact cross_regionCandidate Delta j hlen a false o

/-- **(C) Internal old darts are internal new darts.** -/
theorem regionInternal_embed_iff (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1)
    (z : Delta.toCombMap.Dart) :
    RegionInternal (OuterSpurThickening.regionFamily Delta j hlen family havoid)
        (embed Delta.toCombMap z) ↔ RegionInternal family z := by
  constructor
  · rintro ⟨b, hb, h1, h2⟩
    have hb' : b ∈ family.attach.map
        (OuterSpurThickening.regionFamilyEmbedding Delta j hlen family havoid) := hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hb'
    exact ⟨a.1, a.2,
      ((OuterSpurThickening.embedding Delta j hlen).faceOf_dart_mem_iff a.1.1
        (OuterSpurThickening.outer_not_mem Delta a.1.2) z).mp h1,
      ((OuterSpurThickening.embedding Delta j hlen).faceOf_dart_mem_iff a.1.1
        (OuterSpurThickening.outer_not_mem Delta a.1.2) (Delta.toCombMap.alpha z)).mp h2⟩
  · rintro ⟨a, ha, h1, h2⟩
    exact ⟨OuterSpurThickening.regionFamilyEmbedding Delta j hlen family havoid ⟨a, ha⟩,
      Finset.mem_map_of_mem (OuterSpurThickening.regionFamilyEmbedding Delta j hlen family havoid)
        (Finset.mem_attach family ⟨a, ha⟩),
      ((OuterSpurThickening.embedding Delta j hlen).faceOf_dart_mem_iff a.1
        (OuterSpurThickening.outer_not_mem Delta a.2) z).mpr h1,
      ((OuterSpurThickening.embedding Delta j hlen).faceOf_dart_mem_iff a.1
        (OuterSpurThickening.outer_not_mem Delta a.2) (Delta.toCombMap.alpha z)).mpr h2⟩

/-- **(C) The new dart `none` is not internal.** -/
theorem not_regionInternal_none (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1) :
    ¬ RegionInternal (OuterSpurThickening.regionFamily Delta j hlen family havoid)
      (none : (OuterSpurThickening.diagram Delta j hlen).toCombMap.Dart) := by
  refine not_regionInternal_of_face_not_mem fun b hb h => ?_
  have hb' : b ∈ family.attach.map
      (OuterSpurThickening.regionFamilyEmbedding Delta j hlen family havoid) := hb
  obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp hb'
  obtain ⟨d, hd, -⟩ := ((OuterSpurThickening.embedding Delta j hlen).faceOf_mem_iff c.1.1
    (OuterSpurThickening.outer_not_mem Delta c.1.2) none).mp h
  exact Option.some_ne_none _ hd

/-- **(C) The new dart `some none` is not internal.** -/
theorem not_regionInternal_some_none (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, Delta.toCombMap.faceOf
      (Delta.toCombMap.alpha (FaceEdgeDoubling.dart Delta Delta.outerFace j)) ∉ a.1) :
    ¬ RegionInternal (OuterSpurThickening.regionFamily Delta j hlen family havoid)
      (some none : (OuterSpurThickening.diagram Delta j hlen).toCombMap.Dart) := by
  refine not_regionInternal_of_face_not_mem fun b hb h => ?_
  have hb' : b ∈ family.attach.map
      (OuterSpurThickening.regionFamilyEmbedding Delta j hlen family havoid) := hb
  obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp hb'
  obtain ⟨d, hd, -⟩ := ((OuterSpurThickening.embedding Delta j hlen).faceOf_mem_iff c.1.1
    (OuterSpurThickening.outer_not_mem Delta c.1.2) (some none)).mp h
  exact Option.some_ne_none _ (Option.some.inj hd)

end Crossings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The outer cell doubling transports the family.** -/
noncomputable def transport (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
      (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) ∉ a.1) :
    RegionTransport S (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid) where
  map := OuterSpurThickening.regionFamilyEmbedding S.diagram j hlen S.family havoid
  family_eq := rfl
  cellIndex := (OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv
  source _ := rfl
  target _ := rfl
  profile a :=
    OuterSpurThickening.regionCandidate_profile S.diagram j hlen ⟨a.1, havoid a.1 a.2⟩
  darts := (OuterSpurThickening.embedding S.diagram j hlen).darts
  cross a s o := crossO_regionCandidate S.diagram j hlen ⟨a.1, havoid a.1 a.2⟩ s o

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.crossO_regionCandidate
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.regionInternal_embed_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.transport
