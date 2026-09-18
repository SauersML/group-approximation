import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.Faces
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.InsertNone
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Region-pair thickening: the collapsed rotation and `Φ'_M`

Target: `GroupApproximation.GGT.VanKampen.TwoGonRegionPairStepStatement`.

Notation as in `P05RegionPair/Faces.lean`: `M := S.diagram.toCombMap`,
`w := FaceEdgeDoubling.dart S.diagram f j`, `b := secondCorner ..`, and
`M' := EdgeInsertion.toCombMap M w b` with the new darts `none`, `some none`.

Mathematical proof.

(E) Rotation. The collapsed maps are the restrictions of `M` and `M'` to the non-internal darts,
  and `embed` restricts to an embedding `ιc` of them commuting with `alpha`.  The darts `w`,
  `none` and `some none` are retained; the corner `b` may be internal.  By
  `PhiMapTransport.facePerm_val_of_retained`, the new face rotation at `ιc x` (with `x ≠ w`) is
  `ιc (facePerm x)` unless `facePerm x = w`, in which case it is `some none`.  From `some none` the
  new rotation is the vertex rotation at `none`, which runs past the deleted darts after `b`
  as the old rotation at `α w` does (`facePerm_val_some_none_gen`): it is `ιc (facePerm w)`, or
  `some none` itself when `w` is fixed.  The dart `some none` is not in the range of `ιc`, and `w`
  is not a crossing dart (`not_phiKeepO_dart`), so `phiTransportAt_of_bypass'` applies.

(G) Face classes. `PhiMapTransport.backDart` names each retained new dart by an old one; face-class
  paths are named back (`eqvGen_backDart'`), since `w` and `α w` are not crossing darts.  A new
  dart on the face of a relator cell `i'` is named by an old dart on the old cell face: `none` and
  `embed w` are on the digon, which is not a face image; `some none` is on the face image of `f`,
  so `f` is the old cell face, and `some none` names `w`, which is on `f`.  Otherwise the face of
  `embed z` is the face image of the face of `z`, and by `cell_face_eq` and injectivity of the face
  image, `z` is on the old relator cell `indexEquiv.symm i'`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

open Equiv Embedded Embedded.RegionCandidate PhiMapTransport

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
  (T : RegionPairThickening.StepData S.diagram f j S.family) (hlea : Delta.LeastArea)

/-- Being non-internal is closed under reversal. -/
theorem keepAlpha : ∀ d, ¬ RegionInternal S.family (S.diagram.toCombMap.alpha d) ↔
    ¬ RegionInternal S.family d :=
  fun d => not_congr (regionInternal_alpha S.family d)

/-- An old dart is non-internal after the step exactly when it was before. -/
theorem keepEmbed : ∀ z,
    ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family
      ((stepTransport S f j hlen hf T).darts z) ↔ ¬ RegionInternal S.family z :=
  fun z => not_congr (regionInternal_embed_iff S f j hlen hf T z)

/-- **The embedding of the collapsed maps.** -/
noncomputable def collapsedEmbedding : (collapsedMap S.family).Dart ↪
    (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).Dart where
  toFun x :=
    ⟨(stepTransport S f j hlen hf T).darts x.1, (keepEmbed S f j hlen hf T x.1).mpr x.2⟩
  inj' x y h :=
    Subtype.ext ((stepTransport S f j hlen hf T).darts.injective (congrArg Subtype.val h))

include T in
/-- The doubled dart in the old collapsed map. -/
def wDart : (collapsedMap S.family).Dart :=
  ⟨FaceEdgeDoubling.dart S.diagram f j, dart_not_internal S f j T⟩

/-- The new dart `some none` in the new collapsed map. -/
def sDart : (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).Dart :=
  ⟨some none, someNone_not_internal S f j hlen hf T⟩

theorem collapsedEmbedding_alpha (x : (collapsedMap S.family).Dart) :
    collapsedEmbedding S f j hlen hf T ((collapsedMap S.family).alpha x) =
      (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).alpha
        (collapsedEmbedding S f j hlen hf T x) :=
  Subtype.ext rfl

/-- The new dart `some none` is not an old dart. -/
theorem sDart_not_mem_range :
    sDart S f j hlen hf T ∉ Set.range (collapsedEmbedding S f j hlen hf T) := by
  rintro ⟨x, hx⟩
  have h : (some (some x.1) : EdgeInsertion.Dart S.diagram.toCombMap) = some none :=
    congrArg Subtype.val hx
  exact Option.some_ne_none _ (Option.some.inj h)

include hf hlea in
/-- The doubled dart is not a crossing dart of a component. -/
theorem wDart_not_phiKeepO (a₀ : S.family) :
    ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1) (wDart S f j T) :=
  not_phiKeepO_dart S f j hf T hlea (linkedComponentO_subset S.family a₀.1) (wDart S f j T) rfl

/-- **Rotation away from the doubled dart.** -/
theorem facePerm_collapsed_of_ne (x : (collapsedMap S.family).Dart) (hx : x ≠ wDart S f j T)
    (hfx : (collapsedMap S.family).facePerm x ≠ wDart S f j T) :
    (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).facePerm
        (collapsedEmbedding S f j hlen hf T x) =
      collapsedEmbedding S f j hlen hf T ((collapsedMap S.family).facePerm x) := by
  have hne : ¬ ((collapsedMap S.family).facePerm x).1 = FaceEdgeDoubling.dart S.diagram f j :=
    fun hh => hfx (Subtype.ext hh)
  exact Subtype.ext ((facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d =>
      ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family d)
    (keepAlpha S) (keepAlpha (RegionPairThickening.sectionFamily S f j hlen hf T))
    (keepEmbed S f j hlen hf T) (dart_ne_second S f j hlen) (dart_not_internal S f j T)
    (sigma_alpha_dart S f j hlen) (someNone_not_internal S f j hlen hf T) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_false _ _ (eq_false hne)))

/-- **Rotation into the doubled dart turns to `some none`.** -/
theorem facePerm_collapsed_of_eq (x : (collapsedMap S.family).Dart) (hx : x ≠ wDart S f j T)
    (hfx : (collapsedMap S.family).facePerm x = wDart S f j T) :
    (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).facePerm
        (collapsedEmbedding S f j hlen hf T x) = sDart S f j hlen hf T := by
  have hc : ((collapsedMap S.family).facePerm x).1 = FaceEdgeDoubling.dart S.diagram f j :=
    congrArg Subtype.val hfx
  exact Subtype.ext ((facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d =>
      ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family d)
    (keepAlpha S) (keepAlpha (RegionPairThickening.sectionFamily S f j hlen hf T))
    (keepEmbed S f j hlen hf T) (dart_ne_second S f j hlen) (dart_not_internal S f j T)
    (sigma_alpha_dart S f j hlen) (someNone_not_internal S f j hlen hf T) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_true _ _ (eq_true hc)))

/-- **Rotation from `some none` continues past the doubled dart**, when it is moved. -/
theorem facePerm_sDart_of_ne
    (hne : (collapsedMap S.family).facePerm (wDart S f j T) ≠ wDart S f j T) :
    (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).facePerm
        (sDart S f j hlen hf T) =
      collapsedEmbedding S f j hlen hf T ((collapsedMap S.family).facePerm (wDart S f j T)) := by
  have hne' : ¬ ((collapsedMap S.family).facePerm (wDart S f j T)).1 =
      FaceEdgeDoubling.dart S.diagram f j := fun hh => hne (Subtype.ext hh)
  exact Subtype.ext ((facePerm_val_some_none_gen (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d =>
      ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family d)
    (keepAlpha S) (keepAlpha (RegionPairThickening.sectionFamily S f j hlen hf T))
    (keepEmbed S f j hlen hf T) (dart_ne_second S f j hlen) (dart_not_internal S f j T)
    (sigma_alpha_dart S f j hlen) (someNone_not_internal S f j hlen hf T)
    (none_not_internal S f j hlen hf T)).trans (ite_cond_eq_false _ _ (eq_false hne')))

/-- **Rotation from `some none` returns to it**, when the doubled dart is fixed. -/
theorem facePerm_sDart_of_eq
    (hfix : (collapsedMap S.family).facePerm (wDart S f j T) = wDart S f j T) :
    (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).facePerm
        (sDart S f j hlen hf T) = sDart S f j hlen hf T := by
  have hc : ((collapsedMap S.family).facePerm (wDart S f j T)).1 =
      FaceEdgeDoubling.dart S.diagram f j := congrArg Subtype.val hfix
  exact Subtype.ext ((facePerm_val_some_none_gen (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d =>
      ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family d)
    (keepAlpha S) (keepAlpha (RegionPairThickening.sectionFamily S f j hlen hf T))
    (keepEmbed S f j hlen hf T) (dart_ne_second S f j hlen) (dart_not_internal S f j T)
    (sigma_alpha_dart S f j hlen) (someNone_not_internal S f j hlen hf T)
    (none_not_internal S f j hlen hf T)).trans (ite_cond_eq_true _ _ (eq_true hc)))

/-- **The old dart named by a new collapsed dart.** -/
noncomputable def backCollapsed :
    (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).Dart →
      (collapsedMap S.family).Dart :=
  backDart (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d =>
      ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family d)
    (keepAlpha S) (keepAlpha (RegionPairThickening.sectionFamily S f j hlen hf T))
    (keepEmbed S f j hlen hf T) (dart_not_internal S f j T)

theorem backCollapsed_embedding (x : (collapsedMap S.family).Dart) :
    backCollapsed S f j hlen hf T (collapsedEmbedding S f j hlen hf T x) = x :=
  rfl

include hlea in
/-- **Face-class paths after the step are named back.** -/
theorem eqvGen_backCollapsed (a₀ : S.family)
    (x' y' : (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).Dart)
    (h : Relation.EqvGen (CombMap.FaceClassStep
      (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).dual
      (PhiKeepO (RegionPairThickening.sectionFamily S f j hlen hf T).family
        (linkedComponentO (RegionPairThickening.sectionFamily S f j hlen hf T).family
          ((stepTransport S f j hlen hf T).map a₀)))) x' y') :
    Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1)))
      (backCollapsed S f j hlen hf T x') (backCollapsed S f j hlen hf T y') :=
  eqvGen_backDart' (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d =>
      ¬ RegionInternal (RegionPairThickening.sectionFamily S f j hlen hf T).family d)
    (keepAlpha S) (keepAlpha (RegionPairThickening.sectionFamily S f j hlen hf T))
    (keepEmbed S f j hlen hf T) (dart_ne_second S f j hlen) (dart_not_internal S f j T)
    (sigma_alpha_dart S f j hlen) (someNone_not_internal S f j hlen hf T)
    (none_not_internal S f j hlen hf T)
    (kp := PhiKeepO S.family (linkedComponentO S.family a₀.1))
    (kp' := PhiKeepO (RegionPairThickening.sectionFamily S f j hlen hf T).family
      (linkedComponentO (RegionPairThickening.sectionFamily S f j hlen hf T).family
        ((stepTransport S f j hlen hf T).map a₀)))
    (fun z hz => phiKeepO_map_iff (stepTransport S f j hlen hf T) a₀
      (collapsedEmbedding S f j hlen hf T) (fun _ => rfl) ⟨z, hz⟩)
    (wDart_not_phiKeepO S f j hf T hlea a₀)
    (fun hh => wDart_not_phiKeepO S f j hf T hlea a₀
      ((phiKeepO_alpha (family := S.family) (E := linkedComponentO S.family a₀.1)
        (wDart S f j T)).mp hh))
    h

/-- **A new dart on a relator cell face is named by an old dart on the old cell face.** -/
theorem faceOf_backCollapsed
    (x' : (collapsedMap (RegionPairThickening.sectionFamily S f j hlen hf T).family).Dart)
    (i' : Fin (RegionPairThickening.sectionFamily S f j hlen hf T).diagram.rCellCount)
    (h : (RegionPairThickening.sectionFamily S f j hlen hf T).diagram.toCombMap.faceOf x'.1 =
      (cell (RegionPairThickening.sectionFamily S f j hlen hf T).diagram i').face) :
    S.diagram.toCombMap.faceOf (backCollapsed S f j hlen hf T x').1 =
      (cell S.diagram ((stepTransport S f j hlen hf T).cellIndex.symm i')).face := by
  have hcell := cell_face_eq S f j hlen hf T i'
  obtain ⟨d, _hd⟩ := x'
  rcases d with _ | _ | z
  · exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen _
      ((CellHairThickening.faceOf_none S.diagram f j hlen hf).symm.trans
        (h.trans hcell)).symm).elim
  · have hfc : f = (cell S.diagram ((stepTransport S f j hlen hf T).cellIndex.symm i')).face :=
      FaceEdgeDoubling.faceImage_injective S.diagram f j hlen
        ((FaceEdgeDoubling.faceImage_self S.diagram f j hlen).trans
          ((FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram f j hlen).symm.trans
            (h.trans hcell)))
    exact (FaceEdgeDoubling.dart_face S.diagram f j).trans hfc
  · by_cases hzd : z = FaceEdgeDoubling.dart S.diagram f j
    · subst hzd
      exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen _
        ((CellHairThickening.faceOf_embed_dart S.diagram f j hlen hf).symm.trans
          (h.trans hcell)).symm).elim
    · exact FaceEdgeDoubling.faceImage_injective S.diagram f j hlen
        ((CellHairThickening.faceOf_embed S.diagram f j hlen hf hzd).symm.trans (h.trans hcell))

include hlea in
/-- **`Φ'_M` is carried by the region-pair doubling.** -/
theorem phiTransportAt_step (a₀ : S.family) :
    PhiTransportAt (stepTransport S f j hlen hf T) a₀ :=
  phiTransportAt_of_bypass' (stepTransport S f j hlen hf T) a₀
    (collapsedEmbedding S f j hlen hf T) (fun _ => rfl) (collapsedEmbedding_alpha S f j hlen hf T)
    (sDart_not_mem_range S f j hlen hf T)
    (wDart_not_phiKeepO S f j hf T hlea a₀) (facePerm_collapsed_of_ne S f j hlen hf T)
    (facePerm_collapsed_of_eq S f j hlen hf T) (facePerm_sDart_of_ne S f j hlen hf T)
    (facePerm_sDart_of_eq S f j hlen hf T) (backCollapsed S f j hlen hf T)
    (backCollapsed_embedding S f j hlen hf T) (eqvGen_backCollapsed S f j hlen hf T hlea a₀)
    (faceOf_backCollapsed S f j hlen hf T)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.keepAlpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.keepEmbed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.collapsedEmbedding
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.wDart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.sDart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.collapsedEmbedding_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.sDart_not_mem_range
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.wDart_not_phiKeepO
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.facePerm_collapsed_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.facePerm_collapsed_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.facePerm_sDart_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.facePerm_sDart_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.backCollapsed_embedding
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.eqvGen_backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.faceOf_backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05RegionPair.phiTransportAt_step
