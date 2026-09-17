import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.Collapsed
import GroupApproximation.Meta.AxiomGuard

/-!
# Outer-side thickening preserves a clean two-gon: dart correspondence

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterSideStepStatement`.

Notation. `M := S.diagram.toCombMap`, `w := FaceEdgeDoubling.dart S.diagram outerFace j` (the
first corner `w_j` of the rebased outer boundary), `b := M.facePerm w` (the second corner). The
thickened map `M'` is `EdgeInsertion.toCombMap M w b`, with darts `Option (Option M.Dart)`;
old darts enter through `embed z = some (some z)`, the new edge is `{none, some none}`.
Each old region `r ∈ S.family` becomes `r' := regionCandidate ⟨r, htgt r hr⟩`.

Mathematical proof.

(A) Crossings. For every region `r` and every side `s`, cell side `o`:
  `crossO r' s o = (crossO r s o).map embed`. The source arc is mapped by `embed`; the target
  arc by `targetImage`, which agrees with `embed` on every dart except `alpha w`, and by `htgt`
  the target arc of `r` never contains `alpha w`. `alpha` commutes with `embed` definitionally,
  and the Boolean selector of `crossO false` depends only on whether the target is `none`,
  which is preserved by `target' = target.map indexEquiv`.

(B) Faces. For `z ≠ w`, `faceOf' (embed z) = faceImage (faceOf z)`; `embed w` and `none` lie
  on the new digon, `some none` on the new outer face. New regions consist of face images of
  old region faces; neither the digon nor the new outer face lies in a region.

(C) Internal darts. `RegionInternal family' (embed z) ↔ RegionInternal family z`; the two new
  darts are not internal. Hence the collapsed maps are related by the embedding
  `ιc : x ↦ ⟨embed x, _⟩`, which commutes with `alpha`, and misses `some none`.

(D) Kept darts of the dual Phi map. `PhiKeepO family' E' (ιc x) ↔ PhiKeepO family E x` by (A)
  and injectivity of `embed`, where `E'` is the image of `E`; every kept new dart is in the
  range of `ιc` by (A). The dart `w` is not kept: a crossing on the cell side `true` lies on a
  relator cell face or, for an unbound target, is `alpha` of the head of the target arc, which
  differs from `w` by `htgt`; a crossing on side `false` lies on a region face, and `w` lies on
  the outer face, which belongs to no region.

(E) Rotation. Outside of `w`, the collapsed face rotation of the new map agrees with the old
  one along `ιc`; at the predecessor of `w` it goes to `some none`, and from `some none` it
  continues to `ιc (facePerm w)`. `PhiMapTransport.retainedEquiv_sigma_bypass` then gives an
  equivalence `e` of Phi maps commuting with `alpha` and `sigma`, hence with `facePerm`.

(F) Data. `linkedComponentO family' a₀'` is the image of `linkedComponentO family a₀`, since
  `sideCellO r' s = (sideCellO r s).map indexEquiv`. `ExtPhiData` transports field by field;
  `NoLoops` and `NoMultipleEdges` transport by injectivity of `indexEquiv` and
  `regionCandidate`.

(G) Two-gon. `phiRegionO (e y) = (phiRegionO y)'`, and side, cell side are equal (uniqueness of
  crossings). `IsTwoGon` transports along `e`. A gap-holding corner on the face of `e d` pulls
  back along `e⁻¹` to one on the face of `d` (same target profile). A holding cell on the new
  face pulls back along `backDart` (face class steps), and its cell face is the face image of
  an old relator cell face, whose index is not an end cell of `E` since its image is not an end
  cell of `E'`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

open Equiv Embedded Embedded.RegionCandidate

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
theorem sourceHead (a : OuterDoublingTransport.Transportable Delta j D eps) :
    (OuterDoublingTransport.regionCandidate Delta j hlen a).2.sourceArc.darts.head? =
      a.val.2.sourceArc.darts.head?.map (OuterSpurThickening.embedding Delta j hlen).darts :=
  (congrArg List.head? (CyclicArc.mapTo_darts a.val.2.sourceArc
    (OuterSpurThickening.embedding Delta j hlen).darts
    (OuterSpurThickening.cellDarts_eq Delta j hlen a.val.2.source))).trans List.head?_map

/-- The first dart of a carried target arc. -/
theorem targetHead (a : OuterDoublingTransport.Transportable Delta j D eps) :
    (OuterDoublingTransport.regionCandidate Delta j hlen a).2.targetArc.darts.head? =
      a.val.2.targetArc.darts.head?.map (OuterSpurThickening.embedding Delta j hlen).darts := by
  have h : (OuterDoublingTransport.regionCandidate Delta j hlen a).2.targetArc.darts =
      a.val.2.targetArc.darts.map (OuterSpurThickening.embedding Delta j hlen).darts :=
    (CyclicArc.mapTo_darts a.val.2.targetArc
        (OuterSpurThickening.targetImage Delta j hlen a.val.2.target)
        (OuterSpurThickening.targetDarts_eq Delta j hlen a.val.2.target)).trans
      (List.map_congr_left fun d hd =>
        targetImage_eq Delta j hlen a.val.2.target fun h => a.property (h ▸ hd))
  exact (congrArg List.head? h).trans List.head?_map

theorem cross_regionCandidate_true (a : OuterDoublingTransport.Transportable Delta j D eps)
    (s : Bool) :
    cross (OuterDoublingTransport.regionCandidate Delta j hlen a) s true =
      (cross a.val s true).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases s with
  | false => exact targetHead Delta j hlen a
  | true => exact sourceHead Delta j hlen a

theorem cross_regionCandidate (a : OuterDoublingTransport.Transportable Delta j D eps)
    (s o : Bool) :
    cross (OuterDoublingTransport.regionCandidate Delta j hlen a) s o =
      (cross a.val s o).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases o with
  | true => exact cross_regionCandidate_true Delta j hlen a s
  | false =>
    rw [cross_false, cross_false, cross_regionCandidate_true Delta j hlen a s]
    cases cross a.val s true with
    | none => rfl
    | some _ => rfl

/-- **(A) The crossings of a carried region are the carried crossings.** -/
theorem crossO_regionCandidate (a : OuterDoublingTransport.Transportable Delta j D eps)
    (s o : Bool) :
    crossO (OuterDoublingTransport.regionCandidate Delta j hlen a) s o =
      (crossO a.val s o).map (OuterSpurThickening.embedding Delta j hlen).darts := by
  cases s with
  | true => exact cross_regionCandidate Delta j hlen a true o
  | false =>
    rcases Option.eq_none_or_eq_some a.val.2.target with ht | ⟨i, ht⟩
    · have ht' : (OuterDoublingTransport.regionCandidate Delta j hlen a).2.target = none :=
        congrArg (Option.map (OuterSpurThickening.cellMap Delta j hlen).indexEquiv) ht
      rw [crossO_false_of_eq_none _ ht', crossO_false_of_eq_none _ ht]
      exact cross_regionCandidate Delta j hlen a false (!o)
    · have ht' : (OuterDoublingTransport.regionCandidate Delta j hlen a).2.target =
          some ((OuterSpurThickening.cellMap Delta j hlen).indexEquiv i) :=
        congrArg (Option.map (OuterSpurThickening.cellMap Delta j hlen).indexEquiv) ht
      rw [crossO_false_of_eq_some _ ht', crossO_false_of_eq_some _ ht]
      exact cross_regionCandidate Delta j hlen a false o

end Crossings

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The outer side doubling transports the family.** -/
noncomputable def transport (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
    (htgt : ∀ a ∈ S.family, S.diagram.toCombMap.alpha
      (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) ∉ a.2.targetArc.darts) :
    RegionTransport S (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt) where
  map := OuterDoublingTransport.regionFamilyEmbedding S.diagram j hlen S.family htgt
  family_eq := rfl
  cellIndex := (OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv
  source _ := rfl
  target _ := rfl
  profile a :=
    OuterDoublingTransport.regionCandidate_profile S.diagram j hlen ⟨a.1, htgt a.1 a.2⟩
  darts := (OuterSpurThickening.embedding S.diagram j hlen).darts
  cross a s o := crossO_regionCandidate S.diagram j hlen ⟨a.1, htgt a.1 a.2⟩ s o

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.crossO_regionCandidate
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterSide.transport
