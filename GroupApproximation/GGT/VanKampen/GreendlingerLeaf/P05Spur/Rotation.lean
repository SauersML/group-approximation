import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.Faces
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Outer spur thickening: the collapsed rotation and `Φ'_M`

Target: `GroupApproximation.GGT.VanKampen.TwoGonSpurStepStatement`.

Notation as in `P05Spur/Correspondence.lean`: `M := S.diagram.toCombMap`,
`w := FaceEdgeDoubling.dart S.diagram outerFace j`, `b := secondCorner ..`, and
`M' := EdgeInsertion.toCombMap M w b` with the new darts `none`, `some none`; `hspur` says that
the face across `w` is the outer face.

Mathematical proof.

(E) Rotation. The collapsed maps are the restrictions of `M` and `M'` to the non-internal darts,
  and `embed` restricts to an embedding `ιc` of them commuting with `alpha`.  The darts `w`, `b`,
  `none` and `some none` are all retained.  By `PhiMapTransport.facePerm_val_of_retained`, the new
  face rotation at `ιc x` (with `x ≠ w`) is `ιc (facePerm x)` unless `facePerm x = w`, in which case
  it is `some none`; by `facePerm_val_some_none` it continues from `some none` to `embed b`, and
  `facePerm w = b` (`facePerm_val_self`).  The dart `some none` is not in the range of `ιc`, and
  `w` is not a crossing dart (`not_phiKeepO_dart`: it has the outer face on both sides), so
  `phiTransportAt_of_bypass` applies.

(G) Face classes. `PhiMapTransport.backDart` names each retained new dart by an old one; face-class
  paths are named back (`eqvGen_backDart_of_retained`), since `w` and `alpha w` are not crossing
  darts.  A new dart on the face of a relator cell `i'` is an old dart `z`: `none` is on the digon
  and `some none` on the new outer face, neither a relator cell face; `embed w` is on the digon, and
  the other old darts of the old outer face are on the new outer face.  Otherwise the face of
  `embed z` is the face image of the face of `z`, and by `cell_face_eq` and injectivity of the face
  image, `z` is on the old relator cell `indexEquiv.symm i'`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur

open Equiv Embedded Embedded.RegionCandidate PhiMapTransport

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (hspur : S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha
    (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)) = S.diagram.outerFace)

/-- Being non-internal is closed under reversal. -/
theorem keepAlpha : ∀ d, ¬ RegionInternal S.family (S.diagram.toCombMap.alpha d) ↔
    ¬ RegionInternal S.family d :=
  fun d => not_congr (regionInternal_alpha S.family d)

/-- An old dart is non-internal after the step exactly when it was before. -/
theorem keepEmbed : ∀ z, ¬ RegionInternal (OuterSpurThickening.sectionFamily S j hlen
    hspur).family ((spurTransport S j hlen hspur).darts z) ↔ ¬ RegionInternal S.family z :=
  fun z => not_congr (regionInternal_embed_iff S j hlen hspur z)

/-- **The embedding of the collapsed maps.** -/
noncomputable def collapsedEmbedding : (collapsedMap S.family).Dart ↪
    (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).Dart where
  toFun x := ⟨(spurTransport S j hlen hspur).darts x.1, (keepEmbed S j hlen hspur x.1).mpr x.2⟩
  inj' x y h :=
    Subtype.ext ((spurTransport S j hlen hspur).darts.injective (congrArg Subtype.val h))

/-- The doubled dart in the old collapsed map. -/
def wDart : (collapsedMap S.family).Dart :=
  ⟨FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j, dart_not_internal S j⟩

/-- The new dart `some none` in the new collapsed map. -/
def sDart : (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).Dart :=
  ⟨some none, someNone_not_internal S j hlen hspur⟩

theorem collapsedEmbedding_alpha (x : (collapsedMap S.family).Dart) :
    collapsedEmbedding S j hlen hspur ((collapsedMap S.family).alpha x) =
      (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).alpha
        (collapsedEmbedding S j hlen hspur x) :=
  Subtype.ext rfl

/-- The new dart `some none` is not an old dart. -/
theorem sDart_not_mem_range :
    sDart S j hlen hspur ∉ Set.range (collapsedEmbedding S j hlen hspur) := by
  rintro ⟨x, hx⟩
  have h : (some (some x.1) : EdgeInsertion.Dart S.diagram.toCombMap) = some none :=
    congrArg Subtype.val hx
  exact Option.some_ne_none _ (Option.some.inj h)

include hspur in
/-- The doubled dart is not a crossing dart of a component. -/
theorem wDart_not_phiKeepO (a₀ : S.family) :
    ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1) (wDart S j) :=
  not_phiKeepO_dart S j hspur (wDart S j) rfl

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
    (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).facePerm
        (collapsedEmbedding S j hlen hspur x) =
      collapsedEmbedding S j hlen hspur ((collapsedMap S.family).facePerm x) := by
  have hne : ¬ ((collapsedMap S.family).facePerm x).1 =
      FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j := fun hh => hfx (Subtype.ext hh)
  exact Subtype.ext ((facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSpurThickening.sectionFamily S j hlen hspur).family d)
    (keepAlpha S) (keepAlpha (OuterSpurThickening.sectionFamily S j hlen hspur))
    (keepEmbed S j hlen hspur) (dart_ne_second S j hlen) (dart_not_internal S j)
    (sigma_alpha_dart S j hlen) (someNone_not_internal S j hlen hspur) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_false _ _ (eq_false hne)))

/-- **Rotation into the doubled dart turns to `some none`.** -/
theorem facePerm_collapsed_of_eq (x : (collapsedMap S.family).Dart) (hx : x ≠ wDart S j)
    (hfx : (collapsedMap S.family).facePerm x = wDart S j) :
    (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).facePerm
        (collapsedEmbedding S j hlen hspur x) = sDart S j hlen hspur := by
  have hc : ((collapsedMap S.family).facePerm x).1 =
      FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j := congrArg Subtype.val hfx
  exact Subtype.ext ((facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSpurThickening.sectionFamily S j hlen hspur).family d)
    (keepAlpha S) (keepAlpha (OuterSpurThickening.sectionFamily S j hlen hspur))
    (keepEmbed S j hlen hspur) (dart_ne_second S j hlen) (dart_not_internal S j)
    (sigma_alpha_dart S j hlen) (someNone_not_internal S j hlen hspur) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_true _ _ (eq_true hc)))

/-- **Rotation from `some none` continues past the doubled dart.** -/
theorem facePerm_sDart :
    (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).facePerm
        (sDart S j hlen hspur) =
      collapsedEmbedding S j hlen hspur ((collapsedMap S.family).facePerm (wDart S j)) :=
  Subtype.ext ((facePerm_val_some_none (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSpurThickening.sectionFamily S j hlen hspur).family d)
    (keepAlpha (OuterSpurThickening.sectionFamily S j hlen hspur))
    (keepEmbed S j hlen hspur) (second_not_internal S j hlen)
    (someNone_not_internal S j hlen hspur) (none_not_internal S j hlen hspur)).trans
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
    (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).Dart →
      (collapsedMap S.family).Dart :=
  backDart (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSpurThickening.sectionFamily S j hlen hspur).family d)
    (keepAlpha S) (keepAlpha (OuterSpurThickening.sectionFamily S j hlen hspur))
    (keepEmbed S j hlen hspur) (dart_not_internal S j)

theorem backCollapsed_embedding (x : (collapsedMap S.family).Dart) :
    backCollapsed S j hlen hspur (collapsedEmbedding S j hlen hspur x) = x :=
  rfl

/-- **Face-class paths after the step are named back.** -/
theorem eqvGen_backCollapsed (a₀ : S.family)
    (x' y' : (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).Dart)
    (h : Relation.EqvGen (CombMap.FaceClassStep
      (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).dual
      (PhiKeepO (OuterSpurThickening.sectionFamily S j hlen hspur).family
        (linkedComponentO (OuterSpurThickening.sectionFamily S j hlen hspur).family
          ((spurTransport S j hlen hspur).map a₀)))) x' y') :
    Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1)))
      (backCollapsed S j hlen hspur x') (backCollapsed S j hlen hspur y') :=
  eqvGen_backDart_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSpurThickening.sectionFamily S j hlen hspur).family d)
    (keepAlpha S) (keepAlpha (OuterSpurThickening.sectionFamily S j hlen hspur))
    (keepEmbed S j hlen hspur) (dart_ne_second S j hlen) (dart_not_internal S j)
    (sigma_alpha_dart S j hlen) (second_not_internal S j hlen)
    (someNone_not_internal S j hlen hspur) (none_not_internal S j hlen hspur)
    (kp := PhiKeepO S.family (linkedComponentO S.family a₀.1))
    (kp' := PhiKeepO (OuterSpurThickening.sectionFamily S j hlen hspur).family
      (linkedComponentO (OuterSpurThickening.sectionFamily S j hlen hspur).family
        ((spurTransport S j hlen hspur).map a₀)))
    (fun z hz => phiKeepO_map_iff (spurTransport S j hlen hspur) a₀
      (collapsedEmbedding S j hlen hspur) (fun _ => rfl) ⟨z, hz⟩)
    (wDart_not_phiKeepO S j hspur a₀)
    (fun hh => wDart_not_phiKeepO S j hspur a₀
      ((phiKeepO_alpha (family := S.family) (E := linkedComponentO S.family a₀.1)
        (wDart S j)).mp hh))
    h

/-- **A new dart on a relator cell face is named by an old dart on the old cell face.** -/
theorem faceOf_backCollapsed
    (x' : (collapsedMap (OuterSpurThickening.sectionFamily S j hlen hspur).family).Dart)
    (i' : Fin (OuterSpurThickening.sectionFamily S j hlen hspur).diagram.rCellCount)
    (h : (OuterSpurThickening.sectionFamily S j hlen hspur).diagram.toCombMap.faceOf x'.1 =
      (cell (OuterSpurThickening.sectionFamily S j hlen hspur).diagram i').face) :
    S.diagram.toCombMap.faceOf (backCollapsed S j hlen hspur x').1 =
      (cell S.diagram ((spurTransport S j hlen hspur).cellIndex.symm i')).face := by
  have hcell := cell_face_eq S j hlen hspur i'
  obtain ⟨d, _hd⟩ := x'
  rcases d with _ | _ | z
  · exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen _
      ((FaceEdgeDoubling.faceOf_none_digon S.diagram S.diagram.outerFace j hlen).symm.trans
        (h.trans hcell)).symm).elim
  · exact ((cell (OuterSpurThickening.sectionFamily S j hlen hspur).diagram i').face_ne_outer
      (h.symm.trans
        (FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram S.diagram.outerFace j hlen))).elim
  · have h' : (FaceEdgeDoubling.map S.diagram S.diagram.outerFace j hlen).faceOf
        (EdgeInsertion.embed S.diagram.toCombMap z) =
          (cell (OuterSpurThickening.sectionFamily S j hlen hspur).diagram i').face := h
    by_cases hz : S.diagram.toCombMap.faceOf z = S.diagram.outerFace
    · by_cases hzd : z = FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j
      · have hdig : (FaceEdgeDoubling.map S.diagram S.diagram.outerFace j hlen).faceOf
            (EdgeInsertion.embed S.diagram.toCombMap z) =
              FaceEdgeDoubling.digon S.diagram S.diagram.outerFace j hlen :=
          (congrArg (fun y => (FaceEdgeDoubling.map S.diagram S.diagram.outerFace j hlen).faceOf
            (EdgeInsertion.embed S.diagram.toCombMap y)) hzd).trans
            (FaceEdgeDoubling.faceOf_embed_dart_digon S.diagram S.diagram.outerFace j hlen)
        exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen _
          (hdig.symm.trans (h'.trans hcell)).symm).elim
      · exact ((cell (OuterSpurThickening.sectionFamily S j hlen hspur).diagram
          i').face_ne_outer (h'.symm.trans (FaceEdgeDoubling.faceOf_embed_of_face_of_ne S.diagram
            S.diagram.outerFace j hlen hz hzd))).elim
    · exact FaceEdgeDoubling.faceImage_injective S.diagram S.diagram.outerFace j hlen
        ((FaceEdgeDoubling.faceOf_embed_of_face_ne S.diagram S.diagram.outerFace j hlen hz).symm.trans
          (h'.trans hcell))

/-- **`Φ'_M` is carried by the outer spur thickening.** -/
theorem phiTransportAt (a₀ : S.family) : PhiTransportAt (spurTransport S j hlen hspur) a₀ :=
  phiTransportAt_of_bypass (spurTransport S j hlen hspur) a₀ (collapsedEmbedding S j hlen hspur)
    (fun _ => rfl) (collapsedEmbedding_alpha S j hlen hspur) (sDart_not_mem_range S j hlen hspur)
    (wDart_not_phiKeepO S j hspur a₀) (facePerm_wDart_ne S j hlen)
    (facePerm_collapsed_of_ne S j hlen hspur) (facePerm_collapsed_of_eq S j hlen hspur)
    (facePerm_sDart S j hlen hspur) (backCollapsed S j hlen hspur)
    (backCollapsed_embedding S j hlen hspur) (eqvGen_backCollapsed S j hlen hspur a₀)
    (faceOf_backCollapsed S j hlen hspur)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.facePerm_collapsed_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.eqvGen_backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.faceOf_backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05Spur.phiTransportAt
