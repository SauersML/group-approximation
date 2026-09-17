import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.Crossing
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Outer-cell thickening: the collapsed rotation and `Φ'_M`

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterCellStepStatement`.

Notation as in `P05OuterCell/Crossing.lean`: `M := S.diagram.toCombMap`,
`w := FaceEdgeDoubling.dart S.diagram outerFace j`, `b := secondCorner .. = M.facePerm w`, and
`M' := EdgeInsertion.toCombMap M w b` with the new darts `none`, `some none`.

Mathematical proof.

(D) The doubled dart `w` is not a crossing dart of any `E ⊆ family`: a crossing on cell side `false`
  has its face in the region, but `faceOf w` is the outer face, in no region; a crossing on cell
  side `true` is `alpha` of a crossing on cell side `false`, whose face `faceOf (alpha w)` is in the
  region, against `havoid`.  Neither `w` nor `b` is internal, both lying on the outer face.

(E) Rotation. The collapsed maps are the restrictions of `M` and `M'` to the non-internal darts,
  and `embed` restricts to an embedding `ιc` of them commuting with `alpha`.  The darts `w`, `b`,
  `none` and `some none` are all retained.  By `PhiMapTransport.facePerm_val_of_retained`, the new
  face rotation at `ιc x` (with `x ≠ w`) is `ιc (facePerm x)` unless `facePerm x = w`, in which case
  it is `some none`; by `facePerm_val_some_none` it continues from `some none` to `embed b`, and
  `facePerm w = b` (`facePerm_val_self`).  The dart `some none` is not in the range of `ιc`, and
  `w` is not a crossing dart, so `phiTransportAt_of_bypass` applies.

(F) Face classes. `PhiMapTransport.backDart` names each retained new dart by an old one; face-class
  paths are named back (`eqvGen_backDart_of_retained`), since `w` and `alpha w` are not crossing
  darts.  A new dart on the face of a relator cell `i'` is an old dart `z ≠ w`: `none` and
  `embed w` lie on the digon, which is not a face image, and `some none` lies on the new outer face,
  which is not a relator cell face.  For `z ≠ w` the face of `embed z` is the face image of the face
  of `z`; the face of `i'` is the face image of the face of the old cell `indexEquiv.symm i'`, and
  the face image is injective.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell

open Equiv Embedded Embedded.RegionCandidate PhiMapTransport

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (havoid : ∀ a ∈ S.family, S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
    (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) ∉ a.1)

/-- Being non-internal is closed under reversal. -/
theorem keepAlpha : ∀ d, ¬ RegionInternal S.family (S.diagram.toCombMap.alpha d) ↔
    ¬ RegionInternal S.family d :=
  fun d => not_congr (regionInternal_alpha S.family d)

/-- An old dart is non-internal after the step exactly when it was before. -/
theorem keepEmbed : ∀ z, ¬ RegionInternal (OuterCellThickening.sectionFamilyOfAvoid S j hlen
    havoid).family (EdgeInsertion.embed S.diagram.toCombMap z) ↔ ¬ RegionInternal S.family z :=
  fun z => not_congr (regionInternal_embed_iff S.diagram j hlen S.family havoid z)

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

include havoid in
/-- **(D) The doubled dart is not a crossing dart.** -/
theorem not_phiKeepO_dart {E : Finset (RegionCandidate D eps S.diagram)} (hE : E ⊆ S.family)
    (x : (collapsedMap S.family).Dart)
    (hx : x.1 = FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) :
    ¬ PhiKeepO S.family E x := by
  rintro ⟨a, ha, s, o, h⟩
  rw [hx] at h
  cases o with
  | false =>
    exact OuterSpurThickening.outer_not_mem S.diagram a.2
      (by rw [← FaceEdgeDoubling.dart_face S.diagram S.diagram.outerFace j]; exact faceOf_crossO_false a h)
  | true =>
    have h' : crossO a s false = some (S.diagram.toCombMap.alpha
        (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) := (crossO_alpha a s true _).mpr h
    exact havoid a (hE ha) (faceOf_crossO_false a h')

/-- **The relator cells of the new diagram have the face images of the old cell faces.** -/
theorem cell_face_eq
    (i' : Fin (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).diagram.rCellCount) :
    (cell (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).diagram i').face =
      FaceEdgeDoubling.faceImage S.diagram S.diagram.outerFace j hlen
        (cell S.diagram ((transport S j hlen havoid).cellIndex.symm i')).face :=
  congrArg RelatorCell.face ((congrArg (cell (OuterSpurThickening.diagram S.diagram j hlen))
    ((OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv.apply_symm_apply i').symm).trans
      ((OuterSpurThickening.cellMap S.diagram j hlen).indexed_cell
        ((OuterSpurThickening.cellMap S.diagram j hlen).indexEquiv.symm i')))

/-- **The embedding of the collapsed maps.** -/
noncomputable def collapsedEmbedding : (collapsedMap S.family).Dart ↪
    (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).Dart where
  toFun x := ⟨EdgeInsertion.embed S.diagram.toCombMap x.1, (keepEmbed S j hlen havoid x.1).mpr x.2⟩
  inj' x y h := Subtype.ext (EdgeInsertion.embed_injective S.diagram.toCombMap
    (congrArg Subtype.val h))

/-- The doubled dart in the old collapsed map. -/
def wDart : (collapsedMap S.family).Dart :=
  ⟨FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j, dart_not_internal S j⟩

/-- The new dart `some none` in the new collapsed map. -/
def sDart : (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).Dart :=
  ⟨some none, not_regionInternal_some_none S.diagram j hlen S.family havoid⟩

theorem collapsedEmbedding_alpha (x : (collapsedMap S.family).Dart) :
    collapsedEmbedding S j hlen havoid ((collapsedMap S.family).alpha x) =
      (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).alpha
        (collapsedEmbedding S j hlen havoid x) :=
  Subtype.ext rfl

/-- The new dart `some none` is not an old dart. -/
theorem sDart_not_mem_range :
    sDart S j hlen havoid ∉ Set.range (collapsedEmbedding S j hlen havoid) := by
  rintro ⟨x, hx⟩
  have h : (some (some x.1) : EdgeInsertion.Dart S.diagram.toCombMap) = some none :=
    congrArg Subtype.val hx
  exact Option.some_ne_none _ (Option.some.inj h)

include havoid in
/-- The doubled dart is not a crossing dart of a component. -/
theorem wDart_not_phiKeepO (a₀ : S.family) :
    ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1) (wDart S j) :=
  not_phiKeepO_dart S j havoid (linkedComponentO_subset S.family a₀.1) (wDart S j) rfl

include hlen in
/-- The face rotation moves the doubled dart. -/
theorem facePerm_wDart_ne : (collapsedMap S.family).facePerm (wDart S j) ≠ wDart S j := fun h =>
  dart_ne_second S j hlen ((congrArg Subtype.val h).symm.trans
    (facePerm_val_self (M := S.diagram.toCombMap)
      (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
      (b := EdgeInsertion.secondCorner S.diagram.toCombMap
        (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
        (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
      (keep := fun d => ¬ RegionInternal S.family d)
      (keepAlpha S) (dart_not_internal S j) (sigma_alpha_dart S j hlen)
      (second_not_internal S j hlen)))

/-- **Rotation away from the doubled dart.** -/
theorem facePerm_collapsed_of_ne (x : (collapsedMap S.family).Dart) (hx : x ≠ wDart S j)
    (hfx : (collapsedMap S.family).facePerm x ≠ wDart S j) :
    (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).facePerm
        (collapsedEmbedding S j hlen havoid x) =
      collapsedEmbedding S j hlen havoid ((collapsedMap S.family).facePerm x) := by
  have hne : ¬ ((collapsedMap S.family).facePerm x).1 =
      FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j := fun hh => hfx (Subtype.ext hh)
  exact Subtype.ext ((facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family d)
    (keepAlpha S) (keepAlpha (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid))
    (keepEmbed S j hlen havoid) (dart_ne_second S j hlen) (dart_not_internal S j)
    (sigma_alpha_dart S j hlen) (not_regionInternal_some_none S.diagram j hlen S.family havoid) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_false _ _ (eq_false hne)))

/-- **Rotation into the doubled dart turns to `some none`.** -/
theorem facePerm_collapsed_of_eq (x : (collapsedMap S.family).Dart) (hx : x ≠ wDart S j)
    (hfx : (collapsedMap S.family).facePerm x = wDart S j) :
    (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).facePerm
        (collapsedEmbedding S j hlen havoid x) = sDart S j hlen havoid := by
  have hc : ((collapsedMap S.family).facePerm x).1 =
      FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j := congrArg Subtype.val hfx
  exact Subtype.ext ((facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family d)
    (keepAlpha S) (keepAlpha (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid))
    (keepEmbed S j hlen havoid) (dart_ne_second S j hlen) (dart_not_internal S j)
    (sigma_alpha_dart S j hlen) (not_regionInternal_some_none S.diagram j hlen S.family havoid) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_true _ _ (eq_true hc)))

/-- **Rotation from `some none` continues past the doubled dart.** -/
theorem facePerm_sDart :
    (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).facePerm
        (sDart S j hlen havoid) =
      collapsedEmbedding S j hlen havoid ((collapsedMap S.family).facePerm (wDart S j)) :=
  Subtype.ext ((facePerm_val_some_none (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family d)
    (keepAlpha (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid))
    (keepEmbed S j hlen havoid) (second_not_internal S j hlen)
    (not_regionInternal_some_none S.diagram j hlen S.family havoid)
    (not_regionInternal_none S.diagram j hlen S.family havoid)).trans
    (congrArg (EdgeInsertion.embed S.diagram.toCombMap)
      (facePerm_val_self (M := S.diagram.toCombMap)
        (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
        (b := EdgeInsertion.secondCorner S.diagram.toCombMap
          (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
          (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
        (keep := fun d => ¬ RegionInternal S.family d)
        (keepAlpha S) (dart_not_internal S j) (sigma_alpha_dart S j hlen)
        (second_not_internal S j hlen)).symm))

/-- **The old dart named by a new collapsed dart.** -/
noncomputable def backCollapsed :
    (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).Dart →
      (collapsedMap S.family).Dart :=
  backDart (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family d)
    (keepAlpha S) (keepAlpha (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid))
    (keepEmbed S j hlen havoid) (dart_not_internal S j)

theorem backCollapsed_embedding (x : (collapsedMap S.family).Dart) :
    backCollapsed S j hlen havoid (collapsedEmbedding S j hlen havoid x) = x :=
  rfl

/-- **Face-class paths after the step are named back.** -/
theorem eqvGen_backCollapsed (a₀ : S.family)
    (x' y' : (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).Dart)
    (h : Relation.EqvGen (CombMap.FaceClassStep
      (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).dual
      (PhiKeepO (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family
        (linkedComponentO (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family
          ((transport S j hlen havoid).map a₀)))) x' y') :
    Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1)))
      (backCollapsed S j hlen havoid x') (backCollapsed S j hlen havoid y') :=
  eqvGen_backDart_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family d)
    (keepAlpha S) (keepAlpha (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid))
    (keepEmbed S j hlen havoid) (dart_ne_second S j hlen) (dart_not_internal S j)
    (sigma_alpha_dart S j hlen) (second_not_internal S j hlen)
    (not_regionInternal_some_none S.diagram j hlen S.family havoid)
    (not_regionInternal_none S.diagram j hlen S.family havoid)
    (kp := PhiKeepO S.family (linkedComponentO S.family a₀.1))
    (kp' := PhiKeepO (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family
      (linkedComponentO (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family
        ((transport S j hlen havoid).map a₀)))
    (fun z hz => phiKeepO_map_iff (transport S j hlen havoid) a₀
      (collapsedEmbedding S j hlen havoid) (fun _ => rfl) ⟨z, hz⟩)
    (wDart_not_phiKeepO S j havoid a₀)
    (fun hh => wDart_not_phiKeepO S j havoid a₀
      ((phiKeepO_alpha (family := S.family) (E := linkedComponentO S.family a₀.1)
        (wDart S j)).mp hh))
    h

/-- **A new dart on a relator cell face is named by an old dart on the old cell face.** -/
theorem faceOf_backCollapsed
    (x' : (collapsedMap (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).family).Dart)
    (i' : Fin (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).diagram.rCellCount)
    (h : (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).diagram.toCombMap.faceOf x'.1 =
      (cell (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).diagram i').face) :
    S.diagram.toCombMap.faceOf (backCollapsed S j hlen havoid x').1 =
      (cell S.diagram ((transport S j hlen havoid).cellIndex.symm i')).face := by
  have hcell := cell_face_eq S j hlen havoid i'
  obtain ⟨d, _hd⟩ := x'
  rcases d with _ | _ | z
  · exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen _
      ((OuterCellThickening.faceOf_none S.diagram j hlen).symm.trans (h.trans hcell)).symm).elim
  · exact ((cell (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).diagram i').face_ne_outer
      (h.symm.trans
        (FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram S.diagram.outerFace j hlen))).elim
  · have h' : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
        (EdgeInsertion.embed S.diagram.toCombMap z) =
          (cell (OuterCellThickening.sectionFamilyOfAvoid S j hlen havoid).diagram i').face := h
    by_cases hzd : z = FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j
    · have hdig : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
          (EdgeInsertion.embed S.diagram.toCombMap z) =
            FaceEdgeDoubling.digon S.diagram S.diagram.outerFace j hlen :=
        (congrArg (fun y => (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
          (EdgeInsertion.embed S.diagram.toCombMap y)) hzd).trans
          (OuterCellThickening.faceOf_embed_dart S.diagram j hlen)
      exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen _
        (hdig.symm.trans (h'.trans hcell)).symm).elim
    · exact FaceEdgeDoubling.faceImage_injective S.diagram S.diagram.outerFace j hlen
        ((OuterCellThickening.faceOf_embed S.diagram j hlen hzd).symm.trans (h'.trans hcell))

/-- **`Φ'_M` is carried by the outer cell doubling.** -/
theorem phiTransportAt (a₀ : S.family) : PhiTransportAt (transport S j hlen havoid) a₀ :=
  phiTransportAt_of_bypass (transport S j hlen havoid) a₀ (collapsedEmbedding S j hlen havoid)
    (fun _ => rfl) (collapsedEmbedding_alpha S j hlen havoid) (sDart_not_mem_range S j hlen havoid)
    (wDart_not_phiKeepO S j havoid a₀) (facePerm_wDart_ne S j hlen)
    (facePerm_collapsed_of_ne S j hlen havoid) (facePerm_collapsed_of_eq S j hlen havoid)
    (facePerm_sDart S j hlen havoid) (backCollapsed S j hlen havoid)
    (backCollapsed_embedding S j hlen havoid) (eqvGen_backCollapsed S j hlen havoid a₀)
    (faceOf_backCollapsed S j hlen havoid)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.not_phiKeepO_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.facePerm_collapsed_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.eqvGen_backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.faceOf_backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05OuterCell.phiTransportAt
