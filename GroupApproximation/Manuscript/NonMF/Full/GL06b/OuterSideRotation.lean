import GroupApproximation.Manuscript.NonMF.Full.GL06b.OuterSideTransport
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through an outer side doubling: the collapsed rotation

Target: `GroupApproximation.GGT.VanKampen.TwoGonOuterSideStepStatement` (the outer-side step of
the two-gon clean copy, Osin arXiv:math/0411039v3, Lemma 9.7(b), feeding Lemma 4.4; infrastructure
for `thm:hull`, non_mf_groups_exist.tex ~2121).

Notation as in `OuterSideTransport.lean`: `M := S.diagram.toCombMap`, `o := outerFace`,
`w := FaceEdgeDoubling.dart S.diagram o j`, `b := secondCorner .. = M.facePerm w`, and the doubled
map `M'` is the edge insertion at `w`, `b` with new darts `none` and `some none`.

Mathematical proof.

(F) Rotation.  The collapsed maps keep the non-internal darts, and `embed` restricts to an embedding
  `ιc` of them commuting with `alpha` (internality is carried by `outerSide_regionInternal_embed_iff`).
  The darts `w`, `b`, `none`, `some none` all lie on the old or new exterior or on the digon, so
  they are retained.  The rotation of `M'` at `ιc x` (for `x ≠ w`) is `ιc (facePerm x)`, except
  that it turns to `some none` when `facePerm x = w`; from `some none` it continues to `embed b`,
  and `b = facePerm w`.  The dart `some none` is no old dart, `w` moves under `facePerm` (as
  `w ≠ b`), and `w` is no crossing dart (`outerSide_not_phiKeepO_dart`).

(G) Face classes.  Every retained new dart is named by an old one (`backDart`), and face-class
  paths are named back since neither `w` nor `alpha w` is a crossing dart.  A new dart on the face
  of the relator cell `i'` (the face image of the old cell face) is named by an old dart on the old
  cell face: `none` and `embed w` lie on the digon, which is no face image; `some none` lies on
  the new exterior, which is no relator cell face; and `embed z` for `z ≠ w` lies on
  `faceImage (faceOf z)`, so injectivity of `faceImage` finishes.

(H) Hence `phiTransportAt_of_bypass` applies at every base region (`outerSide_phiTransportAt`).
-/

namespace GroupApproximation.Full.GL06b

open GroupApproximation.GGT.VanKampen GroupApproximation.GGT.VanKampen.Embedded
  GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}
  {D : GGT.RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (j : Fin (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary S.diagram.outerFace).darts.length)
  (htgt : ∀ a ∈ S.family, S.diagram.toCombMap.alpha
    (FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j) ∉ a.2.targetArc.darts)

/-- Being non-internal is closed under reversal (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_keepAlpha {X : DiscDiagram.{u, w, v} W}
    (family : Finset (RegionCandidate D eps X)) :
    ∀ d, ¬ RegionInternal family (X.toCombMap.alpha d) ↔ ¬ RegionInternal family d :=
  fun d => not_congr (regionInternal_alpha family d)

/-- An old dart is non-internal after the step exactly when it was before (Osin Lemma 9.7(b),
outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_keepEmbed : ∀ z, ¬ RegionInternal
    (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
      ((outerSideTransport S j hlen htgt).darts z) ↔ ¬ RegionInternal S.family z :=
  fun z => not_congr (outerSide_regionInternal_embed_iff S j hlen htgt z)

/-- **(F) The embedding of the collapsed maps** (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
noncomputable def outerSide_collapsedEmbedding : (collapsedMap S.family).Dart ↪
    (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).Dart where
  toFun x := ⟨(outerSideTransport S j hlen htgt).darts x.1,
    (outerSide_keepEmbed S j hlen htgt x.1).mpr x.2⟩
  inj' x y h :=
    Subtype.ext ((outerSideTransport S j hlen htgt).darts.injective (congrArg Subtype.val h))

/-- The doubled dart in the old collapsed map (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
def outerSide_wDart : (collapsedMap S.family).Dart :=
  ⟨FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j, outerSide_dart_not_internal S j⟩

/-- The new dart `some none` in the new collapsed map (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
def outerSide_sDart :
    (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).Dart :=
  ⟨some none, outerSide_someNone_not_internal S j hlen htgt⟩

/-- The collapsed embedding commutes with reversal (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_collapsedEmbedding_alpha (x : (collapsedMap S.family).Dart) :
    outerSide_collapsedEmbedding S j hlen htgt ((collapsedMap S.family).alpha x) =
      (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).alpha
        (outerSide_collapsedEmbedding S j hlen htgt x) :=
  Subtype.ext rfl

/-- The new dart `some none` is not an old dart (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_sDart_not_mem_range :
    outerSide_sDart S j hlen htgt ∉ Set.range (outerSide_collapsedEmbedding S j hlen htgt) := by
  rintro ⟨x, hx⟩
  have h : (some (some x.1) : EdgeInsertion.Dart S.diagram.toCombMap) = some none :=
    congrArg Subtype.val hx
  exact Option.some_ne_none _ (Option.some.inj h)

include htgt in
/-- The doubled dart is not a crossing dart of a component (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_wDart_not_phiKeepO (a₀ : S.family) :
    ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1) (outerSide_wDart S j) :=
  outerSide_not_phiKeepO_dart S j htgt (linkedComponentO_subset S.family a₀.1)
    (outerSide_wDart S j) rfl

include hlen in
/-- The face rotation moves the doubled dart (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_facePerm_wDart_ne :
    (collapsedMap S.family).facePerm (outerSide_wDart S j) ≠ outerSide_wDart S j := fun h =>
  outerSide_dart_ne_second S j hlen ((congrArg Subtype.val h).symm.trans
    (PhiMapTransport.facePerm_val_self (M := S.diagram.toCombMap)
      (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
      (b := EdgeInsertion.secondCorner S.diagram.toCombMap
        (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
        (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
      (keep := fun d => ¬ RegionInternal S.family d)
      (outerSide_keepAlpha S.family) (outerSide_dart_not_internal S j)
      (outerSide_sigma_alpha_dart S j hlen) (outerSide_second_not_internal S j hlen)))

/-- **Rotation away from the doubled dart** (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_facePerm_collapsed_of_ne (x : (collapsedMap S.family).Dart)
    (hx : x ≠ outerSide_wDart S j) (hfx : (collapsedMap S.family).facePerm x ≠ outerSide_wDart S j) :
    (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).facePerm
        (outerSide_collapsedEmbedding S j hlen htgt x) =
      outerSide_collapsedEmbedding S j hlen htgt ((collapsedMap S.family).facePerm x) := by
  have hne : ¬ ((collapsedMap S.family).facePerm x).1 =
      FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j :=
    fun hh => hfx (Subtype.ext hh)
  exact Subtype.ext ((PhiMapTransport.facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family d)
    (outerSide_keepAlpha S.family)
    (outerSide_keepAlpha (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family)
    (outerSide_keepEmbed S j hlen htgt) (outerSide_dart_ne_second S j hlen)
    (outerSide_dart_not_internal S j) (outerSide_sigma_alpha_dart S j hlen)
    (outerSide_someNone_not_internal S j hlen htgt) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_false _ _ (eq_false hne)))

/-- **Rotation into the doubled dart turns to `some none`** (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_facePerm_collapsed_of_eq (x : (collapsedMap S.family).Dart)
    (hx : x ≠ outerSide_wDart S j) (hfx : (collapsedMap S.family).facePerm x = outerSide_wDart S j) :
    (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).facePerm
        (outerSide_collapsedEmbedding S j hlen htgt x) = outerSide_sDart S j hlen htgt := by
  have hc : ((collapsedMap S.family).facePerm x).1 =
      FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j :=
    congrArg Subtype.val hfx
  exact Subtype.ext ((PhiMapTransport.facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family d)
    (outerSide_keepAlpha S.family)
    (outerSide_keepAlpha (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family)
    (outerSide_keepEmbed S j hlen htgt) (outerSide_dart_ne_second S j hlen)
    (outerSide_dart_not_internal S j) (outerSide_sigma_alpha_dart S j hlen)
    (outerSide_someNone_not_internal S j hlen htgt) x.2
    (fun hh => hx (Subtype.ext hh))).trans (ite_cond_eq_true _ _ (eq_true hc)))

/-- **Rotation from `some none` continues past the doubled dart** (Osin Lemma 9.7(b), outer-side
step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_facePerm_sDart :
    (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).facePerm
        (outerSide_sDart S j hlen htgt) =
      outerSide_collapsedEmbedding S j hlen htgt
        ((collapsedMap S.family).facePerm (outerSide_wDart S j)) :=
  Subtype.ext ((PhiMapTransport.facePerm_val_some_none (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family d)
    (outerSide_keepAlpha (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family)
    (outerSide_keepEmbed S j hlen htgt) (outerSide_second_not_internal S j hlen)
    (outerSide_someNone_not_internal S j hlen htgt)
    (outerSide_none_not_internal S j hlen htgt)).trans
    (congrArg (EdgeInsertion.embed S.diagram.toCombMap)
      (PhiMapTransport.facePerm_val_self (M := S.diagram.toCombMap)
        (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
        (b := EdgeInsertion.secondCorner S.diagram.toCombMap
          (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
          (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
        (keep := fun d => ¬ RegionInternal S.family d)
        (outerSide_keepAlpha S.family) (outerSide_dart_not_internal S j)
        (outerSide_sigma_alpha_dart S j hlen) (outerSide_second_not_internal S j hlen)).symm))

/-- **(G) The old dart named by a new collapsed dart** (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
noncomputable def outerSide_backCollapsed :
    (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).Dart →
      (collapsedMap S.family).Dart :=
  PhiMapTransport.backDart (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family d)
    (outerSide_keepAlpha S.family)
    (outerSide_keepAlpha (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family)
    (outerSide_keepEmbed S j hlen htgt) (outerSide_dart_not_internal S j)

/-- Naming back undoes the collapsed embedding (Osin Lemma 9.7(b), outer-side step; `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem outerSide_backCollapsed_embedding (x : (collapsedMap S.family).Dart) :
    outerSide_backCollapsed S j hlen htgt (outerSide_collapsedEmbedding S j hlen htgt x) = x :=
  rfl

/-- **Face-class paths after the step are named back** (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_eqvGen_backCollapsed (a₀ : S.family)
    (x' y' :
      (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).Dart)
    (h : Relation.EqvGen (CombMap.FaceClassStep
      (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).dual
      (PhiKeepO (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
        (linkedComponentO (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
          ((outerSideTransport S j hlen htgt).map a₀)))) x' y') :
    Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1)))
      (outerSide_backCollapsed S j hlen htgt x') (outerSide_backCollapsed S j hlen htgt y') :=
  PhiMapTransport.eqvGen_backDart_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j)
    (b := EdgeInsertion.secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram S.diagram.outerFace j)
      (FaceEdgeDoubling.second S.diagram S.diagram.outerFace j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal
      (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family d)
    (outerSide_keepAlpha S.family)
    (outerSide_keepAlpha (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family)
    (outerSide_keepEmbed S j hlen htgt) (outerSide_dart_ne_second S j hlen)
    (outerSide_dart_not_internal S j) (outerSide_sigma_alpha_dart S j hlen)
    (outerSide_second_not_internal S j hlen) (outerSide_someNone_not_internal S j hlen htgt)
    (outerSide_none_not_internal S j hlen htgt)
    (kp := PhiKeepO S.family (linkedComponentO S.family a₀.1))
    (kp' := PhiKeepO (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
      (linkedComponentO (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family
        ((outerSideTransport S j hlen htgt).map a₀)))
    (fun z hz => GreendlingerLeaf.P05CellSide.phiKeepO_map_iff (outerSideTransport S j hlen htgt)
      a₀ (outerSide_collapsedEmbedding S j hlen htgt) (fun _ => rfl) ⟨z, hz⟩)
    (outerSide_wDart_not_phiKeepO S j htgt a₀)
    (fun hh => outerSide_wDart_not_phiKeepO S j htgt a₀
      ((phiKeepO_alpha (family := S.family) (E := linkedComponentO S.family a₀.1)
        (outerSide_wDart S j)).mp hh))
    h

/-- An old dart on a new relator cell face lies on the old cell face (Osin Lemma 9.7(b),
outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_faceOf_embed_of_cell (z : S.diagram.toCombMap.Dart)
    (i' : Fin (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram.rCellCount)
    (h : (OuterSpurThickening.diagram S.diagram j hlen).toCombMap.faceOf
      (EdgeInsertion.embed S.diagram.toCombMap z) =
        (Embedded.cell (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram
          i').face) :
    S.diagram.toCombMap.faceOf z =
      (Embedded.cell S.diagram ((outerSideTransport S j hlen htgt).cellIndex.symm i')).face := by
  have hcell := outerSide_cell_face_eq S j hlen htgt i'
  by_cases hzd : z = FaceEdgeDoubling.dart S.diagram S.diagram.outerFace j
  · have hdig : (FaceEdgeDoubling.map S.diagram S.diagram.outerFace j hlen).faceOf
        (EdgeInsertion.embed S.diagram.toCombMap z) =
          FaceEdgeDoubling.digon S.diagram S.diagram.outerFace j hlen :=
      (congrArg (fun y => (FaceEdgeDoubling.map S.diagram S.diagram.outerFace j hlen).faceOf
        (EdgeInsertion.embed S.diagram.toCombMap y)) hzd).trans
        (FaceEdgeDoubling.faceOf_embed_dart_digon S.diagram S.diagram.outerFace j hlen)
    have h' : (FaceEdgeDoubling.map S.diagram S.diagram.outerFace j hlen).faceOf
        (EdgeInsertion.embed S.diagram.toCombMap z) =
          (Embedded.cell (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram
            i').face := h
    exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen _
      (hdig.symm.trans (h'.trans hcell)).symm).elim
  · exact FaceEdgeDoubling.faceImage_injective S.diagram S.diagram.outerFace j hlen
      ((outerSide_faceOf_embed_of_ne S.diagram j hlen hzd).symm.trans (h.trans hcell))

/-- **A new dart on a relator cell face is named by an old dart on the old cell face** (Osin
Lemma 9.7(b), outer-side step; `thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_faceOf_backCollapsed
    (x' : (collapsedMap (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).family).Dart)
    (i' : Fin (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram.rCellCount)
    (h : (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram.toCombMap.faceOf
      x'.1 = (Embedded.cell (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram
        i').face) :
    S.diagram.toCombMap.faceOf (outerSide_backCollapsed S j hlen htgt x').1 =
      (Embedded.cell S.diagram ((outerSideTransport S j hlen htgt).cellIndex.symm i')).face := by
  have hcell := outerSide_cell_face_eq S j hlen htgt i'
  obtain ⟨d, _hd⟩ := x'
  rcases d with _ | _ | z
  · exact (FaceEdgeDoubling.faceImage_ne_digon S.diagram S.diagram.outerFace j hlen _
      ((FaceEdgeDoubling.faceOf_none_digon S.diagram S.diagram.outerFace j hlen).symm.trans
        (h.trans hcell)).symm).elim
  · have h' : (FaceEdgeDoubling.map S.diagram S.diagram.outerFace j hlen).faceOf
        (some none : EdgeInsertion.Dart S.diagram.toCombMap) =
          (Embedded.cell (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram
            i').face := h
    exact ((Embedded.cell (OuterSideThickening.sectionFamilyOfTransport S j hlen htgt).diagram
      i').face_ne_outer (h'.symm.trans
        (FaceEdgeDoubling.faceOf_some_none_cellFace S.diagram S.diagram.outerFace j hlen))).elim
  · exact outerSide_faceOf_embed_of_cell S j hlen htgt z i' h

/-- **(H) `Φ'_M` is carried by the outer side doubling** (Osin Lemma 9.7(b), outer-side step;
`thm:hull`, non_mf_groups_exist.tex ~2121). -/
theorem outerSide_phiTransportAt (a₀ : S.family) :
    GreendlingerLeaf.P05CellSide.PhiTransportAt (outerSideTransport S j hlen htgt) a₀ :=
  GreendlingerLeaf.P05CellSide.phiTransportAt_of_bypass (outerSideTransport S j hlen htgt) a₀
    (outerSide_collapsedEmbedding S j hlen htgt) (fun _ => rfl)
    (outerSide_collapsedEmbedding_alpha S j hlen htgt) (outerSide_sDart_not_mem_range S j hlen htgt)
    (outerSide_wDart_not_phiKeepO S j htgt a₀) (outerSide_facePerm_wDart_ne S j hlen)
    (outerSide_facePerm_collapsed_of_ne S j hlen htgt)
    (outerSide_facePerm_collapsed_of_eq S j hlen htgt) (outerSide_facePerm_sDart S j hlen htgt)
    (outerSide_backCollapsed S j hlen htgt) (outerSide_backCollapsed_embedding S j hlen htgt)
    (outerSide_eqvGen_backCollapsed S j hlen htgt a₀) (outerSide_faceOf_backCollapsed S j hlen htgt)

end GroupApproximation.Full.GL06b

#audit_axioms GroupApproximation.Full.GL06b.outerSide_keepAlpha
#audit_axioms GroupApproximation.Full.GL06b.outerSide_keepEmbed
#audit_axioms GroupApproximation.Full.GL06b.outerSide_collapsedEmbedding
#audit_axioms GroupApproximation.Full.GL06b.outerSide_wDart
#audit_axioms GroupApproximation.Full.GL06b.outerSide_sDart
#audit_axioms GroupApproximation.Full.GL06b.outerSide_collapsedEmbedding_alpha
#audit_axioms GroupApproximation.Full.GL06b.outerSide_sDart_not_mem_range
#audit_axioms GroupApproximation.Full.GL06b.outerSide_wDart_not_phiKeepO
#audit_axioms GroupApproximation.Full.GL06b.outerSide_facePerm_wDart_ne
#audit_axioms GroupApproximation.Full.GL06b.outerSide_facePerm_collapsed_of_ne
#audit_axioms GroupApproximation.Full.GL06b.outerSide_facePerm_collapsed_of_eq
#audit_axioms GroupApproximation.Full.GL06b.outerSide_facePerm_sDart
#audit_axioms GroupApproximation.Full.GL06b.outerSide_backCollapsed
#audit_axioms GroupApproximation.Full.GL06b.outerSide_backCollapsed_embedding
#audit_axioms GroupApproximation.Full.GL06b.outerSide_eqvGen_backCollapsed
#audit_axioms GroupApproximation.Full.GL06b.outerSide_faceOf_embed_of_cell
#audit_axioms GroupApproximation.Full.GL06b.outerSide_faceOf_backCollapsed
#audit_axioms GroupApproximation.Full.GL06b.outerSide_phiTransportAt
