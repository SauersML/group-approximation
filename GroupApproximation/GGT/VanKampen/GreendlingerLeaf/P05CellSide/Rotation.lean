import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.Doubling
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Cell-side thickening: the collapsed rotation and `Φ'_M`

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellSideStepStatement`.

Notation as in `P05CellSide/Doubling.lean`: `M := S.diagram.toCombMap`, `f ≠ outerFace`,
`w := FaceEdgeDoubling.dart S.diagram f j`, `b := secondCorner ..`, and
`M' := EdgeInsertion.toCombMap M w b` with the new darts `none`, `some none`.

Mathematical proof.

(E) Rotation.  The collapsed maps are the restrictions of `M` and `M'` to the non-internal darts,
  and `embed` restricts to an embedding `ιc` of them commuting with `alpha`.  The darts `w`, `b`,
  `none` and `some none` are all retained.  By `PhiMapTransport.facePerm_val_of_retained`, the new
  face rotation at `ιc x` (with `x ≠ w`) is `ιc (facePerm x)` unless `facePerm x = w`, in which case
  it is `some none`; by `facePerm_val_some_none` it continues from `some none` to `embed b`, and
  `facePerm w = b` (`facePerm_val_self`).  The dart `some none` is not in the range of `ιc`, and
  `w` is not a crossing dart (`not_phiKeepO_dart`), so `phiTransportAt_of_bypass` applies.

(F) Face classes.  `PhiMapTransport.backDart` names each retained new dart by an old one; face-class
  paths are named back (`eqvGen_backDart_of_retained`), since `w` and `alpha w` are not crossing
  darts.  A new dart on the face of a relator cell `i'`, whose face is
  `faceImage (cell S (indexEquiv⁻¹ i')).face`, is named by an old dart on that old cell face:
  `none` and `embed w` are on the digon, which is no face image; `some none` is on
  `cellFace = faceImage f` and is named by `w`, which is on `f`; and `embed z` for `z ≠ w` is on
  `faceImage (faceOf z)`.  Injectivity of `faceImage` finishes each case.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide

open Equiv Embedded Embedded.RegionCandidate PhiMapTransport

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
  (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family)

/-- Being non-internal is closed under reversal. -/
theorem keepAlpha : ∀ d, ¬ RegionInternal S.family (S.diagram.toCombMap.alpha d) ↔
    ¬ RegionInternal S.family d :=
  fun d => not_congr (regionInternal_alpha S.family d)

/-- An old dart is non-internal after the step exactly when it was before. -/
theorem keepEmbed : ∀ z, ¬ RegionInternal (CellSideThickening.sectionFamilyOfArcs S f j hlen hf
    havoid).family ((transport S f j hlen hf havoid).darts z) ↔ ¬ RegionInternal S.family z :=
  fun z => not_congr (regionInternal_embed_iff S f j hlen hf havoid z)

/-- **The embedding of the collapsed maps.** -/
noncomputable def collapsedEmbedding : (collapsedMap S.family).Dart ↪
    (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).Dart where
  toFun x := ⟨(transport S f j hlen hf havoid).darts x.1,
    (keepEmbed S f j hlen hf havoid x.1).mpr x.2⟩
  inj' _ _ h :=
    Subtype.ext ((transport S f j hlen hf havoid).darts.injective (congrArg Subtype.val h))

/-- The doubled dart in the old collapsed map. -/
def wDart : (collapsedMap S.family).Dart :=
  ⟨FaceEdgeDoubling.dart S.diagram f j, dart_not_internal S f j havoid⟩

/-- The new dart `some none` in the new collapsed map. -/
def sDart :
    (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).Dart :=
  ⟨some none, someNone_not_internal S f j hlen hf havoid⟩

theorem collapsedEmbedding_alpha (x : (collapsedMap S.family).Dart) :
    collapsedEmbedding S f j hlen hf havoid ((collapsedMap S.family).alpha x) =
      (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).alpha
        (collapsedEmbedding S f j hlen hf havoid x) :=
  Subtype.ext rfl

/-- The new dart `some none` is not an old dart. -/
theorem sDart_not_mem_range :
    sDart S f j hlen hf havoid ∉ Set.range (collapsedEmbedding S f j hlen hf havoid) := by
  rintro ⟨x, hx⟩
  have h : (some (some x.1) : EdgeInsertion.Dart S.diagram.toCombMap) = some none :=
    congrArg Subtype.val hx
  exact Option.some_ne_none _ (Option.some.inj h)

include hf in
/-- The doubled dart is not a crossing dart of a component. -/
theorem wDart_not_phiKeepO (a₀ : S.family) :
    ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1) (wDart S f j havoid) :=
  not_phiKeepO_dart S f j hf havoid (linkedComponentO_subset S.family a₀.1) (wDart S f j havoid) rfl

include hlen in
/-- The face rotation moves the doubled dart. -/
theorem facePerm_wDart_ne :
    (collapsedMap S.family).facePerm (wDart S f j havoid) ≠ wDart S f j havoid := fun h =>
  dart_ne_second S f j hlen ((congrArg Subtype.val h).symm.trans
    (facePerm_val_self (M := S.diagram.toCombMap)
      (a := FaceEdgeDoubling.dart S.diagram f j)
      (b := EdgeInsertion.secondCorner S.diagram.toCombMap
        (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen))
      (keep := fun d => ¬ RegionInternal S.family d)
      (keepAlpha S) (dart_not_internal S f j havoid) (sigma_alpha_dart S f j hlen)
      (second_not_internal S f j hlen havoid)))

/-- **Rotation away from the doubled dart.** -/
theorem facePerm_collapsed_of_ne (x : (collapsedMap S.family).Dart) (hx : x ≠ wDart S f j havoid)
    (hfx : (collapsedMap S.family).facePerm x ≠ wDart S f j havoid) :
    (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).facePerm
        (collapsedEmbedding S f j hlen hf havoid x) =
      collapsedEmbedding S f j hlen hf havoid ((collapsedMap S.family).facePerm x) := by
  have hne : ¬ ((collapsedMap S.family).facePerm x).1 = FaceEdgeDoubling.dart S.diagram f j :=
    fun hh => hfx (Subtype.ext hh)
  exact Subtype.ext ((facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family d)
    (keepAlpha S) (keepAlpha (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid))
    (keepEmbed S f j hlen hf havoid) (dart_ne_second S f j hlen) (dart_not_internal S f j havoid)
    (sigma_alpha_dart S f j hlen) (someNone_not_internal S f j hlen hf havoid) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_false _ _ (eq_false hne)))

/-- **Rotation into the doubled dart turns to `some none`.** -/
theorem facePerm_collapsed_of_eq (x : (collapsedMap S.family).Dart) (hx : x ≠ wDart S f j havoid)
    (hfx : (collapsedMap S.family).facePerm x = wDart S f j havoid) :
    (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).facePerm
        (collapsedEmbedding S f j hlen hf havoid x) = sDart S f j hlen hf havoid := by
  have hc : ((collapsedMap S.family).facePerm x).1 = FaceEdgeDoubling.dart S.diagram f j :=
    congrArg Subtype.val hfx
  exact Subtype.ext ((facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family d)
    (keepAlpha S) (keepAlpha (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid))
    (keepEmbed S f j hlen hf havoid) (dart_ne_second S f j hlen) (dart_not_internal S f j havoid)
    (sigma_alpha_dart S f j hlen) (someNone_not_internal S f j hlen hf havoid) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_true _ _ (eq_true hc)))

/-- **Rotation from `some none` continues past the doubled dart.** -/
theorem facePerm_sDart :
    (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).facePerm
        (sDart S f j hlen hf havoid) =
      collapsedEmbedding S f j hlen hf havoid
        ((collapsedMap S.family).facePerm (wDart S f j havoid)) :=
  Subtype.ext ((facePerm_val_some_none (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family d)
    (keepAlpha (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid))
    (keepEmbed S f j hlen hf havoid) (second_not_internal S f j hlen havoid)
    (someNone_not_internal S f j hlen hf havoid) (none_not_internal S f j hlen hf havoid)).trans
    (congrArg (EdgeInsertion.embed S.diagram.toCombMap)
      (facePerm_val_self (M := S.diagram.toCombMap)
        (a := FaceEdgeDoubling.dart S.diagram f j)
        (b := EdgeInsertion.secondCorner S.diagram.toCombMap
          (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen))
        (keep := fun d => ¬ RegionInternal S.family d)
        (keepAlpha S) (dart_not_internal S f j havoid) (sigma_alpha_dart S f j hlen)
        (second_not_internal S f j hlen havoid)).symm))

/-- **The old dart named by a new collapsed dart.** -/
noncomputable def backCollapsed :
    (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).Dart →
      (collapsedMap S.family).Dart :=
  backDart (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family d)
    (keepAlpha S) (keepAlpha (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid))
    (keepEmbed S f j hlen hf havoid) (dart_not_internal S f j havoid)

theorem backCollapsed_embedding (x : (collapsedMap S.family).Dart) :
    backCollapsed S f j hlen hf havoid (collapsedEmbedding S f j hlen hf havoid x) = x :=
  rfl

/-- **Face-class paths after the step are named back.** -/
theorem eqvGen_backCollapsed (a₀ : S.family)
    (x' y' :
      (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).Dart)
    (h : Relation.EqvGen (CombMap.FaceClassStep
      (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).dual
      (PhiKeepO (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family
        (linkedComponentO (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family
          ((transport S f j hlen hf havoid).map a₀)))) x' y') :
    Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1)))
      (backCollapsed S f j hlen hf havoid x') (backCollapsed S f j hlen hf havoid y') :=
  eqvGen_backDart_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family d)
    (keepAlpha S) (keepAlpha (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid))
    (keepEmbed S f j hlen hf havoid) (dart_ne_second S f j hlen) (dart_not_internal S f j havoid)
    (sigma_alpha_dart S f j hlen) (second_not_internal S f j hlen havoid)
    (someNone_not_internal S f j hlen hf havoid) (none_not_internal S f j hlen hf havoid)
    (kp := PhiKeepO S.family (linkedComponentO S.family a₀.1))
    (kp' := PhiKeepO (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family
      (linkedComponentO (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family
        ((transport S f j hlen hf havoid).map a₀)))
    (fun z hz => phiKeepO_map_iff (transport S f j hlen hf havoid) a₀
      (collapsedEmbedding S f j hlen hf havoid) (fun _ => rfl) ⟨z, hz⟩)
    (wDart_not_phiKeepO S f j hf havoid a₀)
    (fun hh => wDart_not_phiKeepO S f j hf havoid a₀
      ((phiKeepO_alpha (family := S.family) (E := linkedComponentO S.family a₀.1)
        (wDart S f j havoid)).mp hh))
    h

/-- An old dart other than the doubled one on a new relator cell face lies on the old cell face. -/
theorem faceOf_embed_of_cell (z : S.diagram.toCombMap.Dart)
    (i' : Fin (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram.rCellCount)
    (h : (FaceEdgeDoubling.diagram S.diagram f j hlen hf).toCombMap.faceOf
      ((FaceEdgeDoubling.embedding S.diagram f j hlen hf).darts z) =
        (cell (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram i').face) :
    S.diagram.toCombMap.faceOf z =
      (cell S.diagram ((transport S f j hlen hf havoid).cellIndex.symm i')).face := by
  have hcell := cell_face_eq S f j hlen hf havoid i'
  by_cases hzd : z = FaceEdgeDoubling.dart S.diagram f j
  · have hdig : (FaceEdgeDoubling.map S.diagram f j hlen).faceOf
        (EdgeInsertion.embed S.diagram.toCombMap z) = FaceEdgeDoubling.digon S.diagram f j hlen :=
      (congrArg (fun y => (FaceEdgeDoubling.map S.diagram f j hlen).faceOf
        (EdgeInsertion.embed S.diagram.toCombMap y)) hzd).trans
        (FaceEdgeDoubling.faceOf_embed_dart_digon S.diagram f j hlen)
    have h' : (FaceEdgeDoubling.map S.diagram f j hlen).faceOf
        (EdgeInsertion.embed S.diagram.toCombMap z) =
          (cell (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram i').face := h
    exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen _
      (hdig.symm.trans (h'.trans hcell)).symm).elim
  · exact FaceEdgeDoubling.faceImage_injective S.diagram f j hlen
      ((FaceEdgeDoubling.faceOf_diagram_embed_of_ne S.diagram f j hlen hf hzd).symm.trans
        (h.trans hcell))

/-- **A new dart on a relator cell face is named by an old dart on the old cell face.** -/
theorem faceOf_backCollapsed
    (x' : (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).Dart)
    (i' : Fin (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram.rCellCount)
    (h : (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram.toCombMap.faceOf
      x'.1 = (cell (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram i').face) :
    S.diagram.toCombMap.faceOf (backCollapsed S f j hlen hf havoid x').1 =
      (cell S.diagram ((transport S f j hlen hf havoid).cellIndex.symm i')).face := by
  have hcell := cell_face_eq S f j hlen hf havoid i'
  obtain ⟨d, _hd⟩ := x'
  rcases d with _ | _ | z
  · exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen _
      ((FaceEdgeDoubling.faceOf_none_digon S.diagram f j hlen).symm.trans
        (h.trans hcell)).symm).elim
  · have h' : (FaceEdgeDoubling.map S.diagram f j hlen).faceOf
        (some none : EdgeInsertion.Dart S.diagram.toCombMap) =
          (cell (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).diagram i').face := h
    have hf' : f = (cell S.diagram ((transport S f j hlen hf havoid).cellIndex.symm i')).face :=
      FaceEdgeDoubling.faceImage_injective S.diagram f j hlen
        ((FaceEdgeDoubling.faceImage_self S.diagram f j hlen).trans
          ((FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram f j hlen).symm.trans
            (h'.trans hcell)))
    show S.diagram.toCombMap.faceOf (FaceEdgeDoubling.dart S.diagram f j) = _
    exact (FaceEdgeDoubling.dart_face S.diagram f j).trans hf'
  · exact faceOf_embed_of_cell S f j hlen hf havoid z i' h

/-- **`Φ'_M` is carried by the cell-side doubling.** -/
theorem phiTransportAt (a₀ : S.family) : PhiTransportAt (transport S f j hlen hf havoid) a₀ :=
  phiTransportAt_of_bypass (transport S f j hlen hf havoid) a₀
    (collapsedEmbedding S f j hlen hf havoid) (fun _ => rfl)
    (collapsedEmbedding_alpha S f j hlen hf havoid) (sDart_not_mem_range S f j hlen hf havoid)
    (wDart_not_phiKeepO S f j hf havoid a₀) (facePerm_wDart_ne S f j hlen havoid)
    (facePerm_collapsed_of_ne S f j hlen hf havoid) (facePerm_collapsed_of_eq S f j hlen hf havoid)
    (facePerm_sDart S f j hlen hf havoid) (backCollapsed S f j hlen hf havoid)
    (backCollapsed_embedding S f j hlen hf havoid) (eqvGen_backCollapsed S f j hlen hf havoid a₀)
    (faceOf_backCollapsed S f j hlen hf havoid)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.facePerm_collapsed_of_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.eqvGen_backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.faceOf_backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.phiTransportAt
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.keepAlpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.keepEmbed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.collapsedEmbedding
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.wDart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.sDart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.collapsedEmbedding_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.sDart_not_mem_range
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.wDart_not_phiKeepO
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.facePerm_wDart_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.facePerm_collapsed_of_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.facePerm_sDart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.backCollapsed_embedding
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellSide.faceOf_embed_of_cell
