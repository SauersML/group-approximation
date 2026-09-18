import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.Doubling
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerPhiMapTransportClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Opening a cell hair preserves a clean two-gon: the rotation of `Φ'_M`

Target: `GroupApproximation.GGT.VanKampen.TwoGonCellHairStepStatement`.

Notation as in `P05CellHair/Doubling`: `M := S.diagram.toCombMap`, `w := FaceEdgeDoubling.dart`,
`b := secondCorner = M.facePerm w`, `M' := EdgeInsertion.toCombMap M w b`,
`embed z = some (some z)`, `S'` the opened family and `T := transport S f j hlen hf havoid`.

Mathematical proof.

(C') Kept darts.  `w` lies on `f` and `b = facePerm w` lies on `f`; `f` is in no region of `S`, so
  neither is internal.  `none` lies on the digon and `some none` on `cellFace`; a new region is made
  of face images `keep g` with `g ≠ f`, which are neither, so neither new dart is internal.
  Internal darts correspond along `embed` (`regionInternal_embed_iff`).  Hence
  `ιc x := ⟨embed x, _⟩` embeds the collapsed maps; it commutes with `alpha` definitionally, its
  first coordinate is `T.darts`, and it misses `some none`.

(D') `w` is not a crossing of any component: a crossing `crossO r s false = some w` puts
  `faceOf w = f` in `r.1`; a crossing `crossO r s true = some w` gives
  `crossO r s false = some (alpha w)`, putting the face across `w` in `r.1`; both are excluded by
  `havoid`.

(E') Rotation.  By `PhiMapTransport.facePerm_val_self`, the collapsed rotation at `w` is `b`, and
  `b ≠ w`.  By `facePerm_val_of_retained`, for a kept `z ≠ w`, the new collapsed rotation at
  `embed z` is `some none` if the old one reaches `w`, and `embed` of the old one otherwise.  By
  `facePerm_val_some_none`, the new rotation at `some none` is `embed b = ιc (facePerm w)`.  These
  are exactly the bypass hypotheses `h0`, `h1`, `h2`, `h3` of `phiTransportAt_of_bypass`.

(F') Naming back.  `back := PhiMapTransport.backDart` names `embed z` by `z`, `some none` by `w`,
  `none` by `alpha w`; `back (ιc x) = x`.  Neither `w` nor `alpha w` is a crossing (by (D') and
  `phiKeepO_alpha`), and crossings correspond along `ιc` (`phiKeepO_map_iff`), so
  `eqvGen_backDart_of_retained` names every face-class path after the step by one before it.
  Relator cell faces: `cell S' i'` has face `faceImage (cell S (indexEquiv⁻¹ i')).face`.  If a dart
  `x'` of `M'` lies on it: `none` and `embed w` lie on the digon, which is no face image;
  `some none` lies on `faceImage (faceOf w)`, so injectivity of `faceImage` gives
  `faceOf w = (cell S _).face`; `embed z` with `z ≠ w` lies on `faceImage (faceOf z)`, so
  `faceOf z = (cell S _).face`.

(G') `phiTransportAt_of_bypass` gives `PhiTransportAt T a₀` for every `a₀`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

open Equiv EdgeInsertion Embedded Embedded.RegionCandidate PhiMapTransport

universe u w v

section Faces

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {eps : ℕ} (X : DiscDiagram.{u, w, v} W) (f : X.toCombMap.Face)
  (j : Fin (X.faceBoundary f).darts.length)
  (hlen : 1 < (X.faceBoundary f).darts.length) (hf : f ≠ X.outerFace)

/-- Being kept is invariant under reversal. -/
theorem keep_alpha {Y : DiscDiagram.{u, w, v} W} (family : Finset (RegionCandidate D eps Y))
    (d : Y.toCombMap.Dart) :
    ¬ RegionInternal family (Y.toCombMap.alpha d) ↔ ¬ RegionInternal family d :=
  not_congr (regionInternal_alpha family d)

/-- The old rotation from `alpha w` is the second corner. -/
theorem sigma_alpha_dart :
    X.toCombMap.sigma (X.toCombMap.alpha (FaceEdgeDoubling.dart X f j)) =
      secondCorner X.toCombMap (FaceEdgeDoubling.rebased X f j)
        (FaceEdgeDoubling.second X f j hlen) :=
  (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm X f j hlen).symm

/-- The two corners differ. -/
theorem dart_ne_second :
    FaceEdgeDoubling.dart X f j ≠
      secondCorner X.toCombMap (FaceEdgeDoubling.rebased X f j)
        (FaceEdgeDoubling.second X f j hlen) := fun h =>
  FaceEdgeDoubling.Holding.facePerm_dart_ne X f j hlen
    ((FaceEdgeDoubling.Holding.secondCorner_eq_facePerm X f j hlen).symm.trans h.symm)

/-- The dart `some none` lies on the image of the face of `w`. -/
theorem faceOf_some_none_image :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf (some none) =
      FaceEdgeDoubling.faceImage X f j hlen (X.toCombMap.faceOf (FaceEdgeDoubling.dart X f j)) :=
  (congrArg (FaceEdgeDoubling.map X f j hlen).faceOf
    (FaceEdgeDoubling.Holding.dartImage_dart X f j hlen).symm).trans
    (FaceEdgeDoubling.Holding.faceOf_dartImage X f j hlen (FaceEdgeDoubling.dart X f j))

/-- The dart `some none` lies on `cellFace`. -/
theorem faceOf_some_none :
    (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.faceOf (some none) =
      FaceEdgeDoubling.cellFace X f j hlen :=
  (faceOf_some_none_image X f j hlen hf).trans
    (by rw [FaceEdgeDoubling.dart_face, FaceEdgeDoubling.faceImage_self])

/-- **A face that is no image `keep g`, `g ≠ f`, lies in no carried region.** -/
theorem face_not_mem_regionFamily (family : Finset (RegionCandidate D eps X))
    (havoid : ∀ a ∈ family, f ∉ a.1 ∧
      X.toCombMap.faceOf (X.toCombMap.alpha (FaceEdgeDoubling.dart X f j)) ∉ a.1)
    {F : (FaceEdgeDoubling.diagram X f j hlen hf).toCombMap.Face}
    (hF : ∀ g, g ≠ f → FaceEdgeDoubling.keep X f j hlen g ≠ F)
    {r : RegionCandidate D eps (FaceEdgeDoubling.diagram X f j hlen hf)}
    (hr : r ∈ FaceEdgeDoubling.regionFamily X f j hlen hf family havoid) : F ∉ r.1 := by
  obtain ⟨b, hb, hrb⟩ := FaceEdgeDoubling.regionFamily_faces X f j hlen hf family havoid hr
  rw [hrb]
  intro h
  obtain ⟨g, hg, hgF⟩ := Finset.mem_map.mp h
  exact hF g (fun hgf => (havoid b hb).1 (by rw [← hgf]; exact hg)) hgF

/-- **The faces of the renumbered relator cells.** -/
theorem cell_face_eq (i' : Fin (FaceEdgeDoubling.diagram X f j hlen hf).rCellCount) :
    (Embedded.cell (FaceEdgeDoubling.diagram X f j hlen hf) i').face =
      FaceEdgeDoubling.faceImage X f j hlen (Embedded.cell X
        ((FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv.symm i')).face := by
  have h := (FaceEdgeDoubling.cellMap X f j hlen hf).indexed_cell
    ((FaceEdgeDoubling.cellMap X f j hlen hf).indexEquiv.symm i')
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  exact (FaceEdgeDoubling.cellMap X f j hlen hf).face_eq _

end Faces

section Keep

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
  (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
    (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1)

include havoid in
/-- **(C') The dart `w` is kept.** -/
theorem dart_keep : ¬ RegionInternal S.family (FaceEdgeDoubling.dart S.diagram f j) :=
  not_regionInternal_of_face_not_mem fun r hr h =>
    (havoid r hr).1 (by rwa [FaceEdgeDoubling.dart_face] at h)

include havoid in
/-- **(C') The second corner is kept.** -/
theorem second_keep :
    ¬ RegionInternal S.family (secondCorner S.diagram.toCombMap
      (FaceEdgeDoubling.rebased S.diagram f j) (FaceEdgeDoubling.second S.diagram f j hlen)) :=
  not_regionInternal_of_face_not_mem fun r hr h =>
    (havoid r hr).1 (by
      rwa [FaceEdgeDoubling.Holding.secondCorner_eq_facePerm, CombMap.faceOf_facePerm,
        FaceEdgeDoubling.dart_face] at h)

/-- **(C') The new dart `some none` is kept.** -/
theorem some_none_keep :
    ¬ RegionInternal (HairOpening.sectionFamily S f j hlen hf havoid).family
      (some none : (FaceEdgeDoubling.map S.diagram f j hlen).Dart) :=
  not_regionInternal_of_face_not_mem fun r hr h =>
    face_not_mem_regionFamily S.diagram f j hlen hf S.family havoid
      (F := (FaceEdgeDoubling.diagram S.diagram f j hlen hf).toCombMap.faceOf (some none))
      (fun g hg e => FaceEdgeDoubling.keep_ne_cellFace S.diagram f j hlen hg
        (e.trans (faceOf_some_none S.diagram f j hlen hf))) hr h

/-- **(C') The new dart `none` is kept.** -/
theorem none_keep :
    ¬ RegionInternal (HairOpening.sectionFamily S f j hlen hf havoid).family
      (none : (FaceEdgeDoubling.map S.diagram f j hlen).Dart) :=
  not_regionInternal_of_face_not_mem fun r hr h =>
    face_not_mem_regionFamily S.diagram f j hlen hf S.family havoid
      (F := (FaceEdgeDoubling.diagram S.diagram f j hlen hf).toCombMap.faceOf none)
      (fun g hg e => FaceEdgeDoubling.keep_ne_digon S.diagram f j hlen hg
        (e.trans (CellHairThickening.faceOf_none S.diagram f j hlen hf))) hr h

/-- **(C') Embedded darts are kept exactly when they were kept.** -/
theorem embed_keep_iff (z : S.diagram.toCombMap.Dart) :
    ¬ RegionInternal (HairOpening.sectionFamily S f j hlen hf havoid).family
        (embed S.diagram.toCombMap z) ↔ ¬ RegionInternal S.family z :=
  not_congr (regionInternal_embed_iff S.diagram f j hlen hf S.family havoid z)

end Keep

section Rotation

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
  (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
  (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
  (havoid : ∀ a ∈ S.family, f ∉ a.1 ∧ S.diagram.toCombMap.faceOf
    (S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j)) ∉ a.1)

include hlen in
/-- **(E') The old collapsed rotation at `w`** is the old rotation at `w`. -/
theorem facePerm_dart :
    ((collapsedMap S.family).facePerm
        ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩).1 =
      S.diagram.toCombMap.facePerm (FaceEdgeDoubling.dart S.diagram f j) :=
  (facePerm_val_self (M := S.diagram.toCombMap) (a := FaceEdgeDoubling.dart S.diagram f j)
      (b := secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
        (FaceEdgeDoubling.second S.diagram f j hlen))
      (keep := fun d => ¬ RegionInternal S.family d) (keep_alpha S.family)
      (dart_keep S f j havoid) (sigma_alpha_dart S.diagram f j hlen)
      (second_keep S f j hlen havoid)).trans
    (FaceEdgeDoubling.Holding.secondCorner_eq_facePerm S.diagram f j hlen)

include hlen in
/-- **(E') The old collapsed rotation moves `w`.** -/
theorem facePerm_w_ne :
    (collapsedMap S.family).facePerm
        ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩ ≠
      ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩ := fun h =>
  FaceEdgeDoubling.Holding.facePerm_dart_ne S.diagram f j hlen
    ((facePerm_dart S f j hlen havoid).symm.trans (congrArg Subtype.val h))

/-- **(C') The collapsed maps embed along `embed`.** -/
noncomputable def collapsedEmbed :
    (collapsedMap S.family).Dart ↪
      (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).Dart where
  toFun x := ⟨embed S.diagram.toCombMap x.1,
    fun h => x.2 ((regionInternal_embed_iff S.diagram f j hlen hf S.family havoid x.1).mp h)⟩
  inj' x y h := Subtype.ext (EdgeInsertion.embed_injective _ (congrArg Subtype.val h))

/-- **(C') The embedding commutes with reversal.** -/
theorem collapsedEmbed_alpha (x : (collapsedMap S.family).Dart) :
    collapsedEmbed S f j hlen hf havoid ((collapsedMap S.family).alpha x) =
      (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).alpha
        (collapsedEmbed S f j hlen hf havoid x) :=
  Subtype.ext rfl

/-- **(C') The new dart `some none` is not an old dart.** -/
theorem some_none_not_mem_range :
    (⟨some none, some_none_keep S f j hlen hf havoid⟩ :
        (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).Dart) ∉
      Set.range (collapsedEmbed S f j hlen hf havoid) := by
  rintro ⟨_, hx⟩
  have hv := congrArg Subtype.val hx
  exact Option.some_ne_none _ (Option.some.inj hv)

/-- **(E') Away from `w`, the rotations agree along the embedding.** -/
theorem rotation_away (x : (collapsedMap S.family).Dart)
    (hxw : x ≠ ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩)
    (hfx : (collapsedMap S.family).facePerm x ≠
      ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩) :
    (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).facePerm
        (collapsedEmbed S f j hlen hf havoid x) =
      collapsedEmbed S f j hlen hf havoid ((collapsedMap S.family).facePerm x) := by
  obtain ⟨z, hz⟩ := x
  have h := facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal (HairOpening.sectionFamily S f j hlen hf havoid).family d)
    (keep_alpha S.family) (keep_alpha (HairOpening.sectionFamily S f j hlen hf havoid).family)
    (embed_keep_iff S f j hlen hf havoid) (dart_ne_second S.diagram f j hlen)
    (dart_keep S f j havoid) (sigma_alpha_dart S.diagram f j hlen)
    (some_none_keep S f j hlen hf havoid) hz (fun e => hxw (Subtype.ext e))
  split_ifs at h with hc
  · exact (hfx (Subtype.ext hc)).elim
  · exact Subtype.ext h

/-- **(E') Into `w`, the new rotation detours to `some none`.** -/
theorem rotation_into (x : (collapsedMap S.family).Dart)
    (hxw : x ≠ ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩)
    (hfx : (collapsedMap S.family).facePerm x =
      ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩) :
    (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).facePerm
        (collapsedEmbed S f j hlen hf havoid x) =
      ⟨some none, some_none_keep S f j hlen hf havoid⟩ := by
  obtain ⟨z, hz⟩ := x
  have h := facePerm_val_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal (HairOpening.sectionFamily S f j hlen hf havoid).family d)
    (keep_alpha S.family) (keep_alpha (HairOpening.sectionFamily S f j hlen hf havoid).family)
    (embed_keep_iff S f j hlen hf havoid) (dart_ne_second S.diagram f j hlen)
    (dart_keep S f j havoid) (sigma_alpha_dart S.diagram f j hlen)
    (some_none_keep S f j hlen hf havoid) hz (fun e => hxw (Subtype.ext e))
  split_ifs at h with hc
  · exact Subtype.ext h
  · exact (hc (congrArg Subtype.val hfx)).elim

/-- **(E') From `some none`, the new rotation returns to the rotation of `w`.** -/
theorem rotation_out :
    (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).facePerm
        ⟨some none, some_none_keep S f j hlen hf havoid⟩ =
      collapsedEmbed S f j hlen hf havoid ((collapsedMap S.family).facePerm
        ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩) :=
  Subtype.ext ((facePerm_val_some_none (M := S.diagram.toCombMap)
      (a := FaceEdgeDoubling.dart S.diagram f j)
      (b := secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
        (FaceEdgeDoubling.second S.diagram f j hlen))
      (keep := fun d => ¬ RegionInternal S.family d)
      (keep' := fun d => ¬ RegionInternal (HairOpening.sectionFamily S f j hlen hf havoid).family d)
      (keep_alpha (HairOpening.sectionFamily S f j hlen hf havoid).family)
      (embed_keep_iff S f j hlen hf havoid) (second_keep S f j hlen havoid)
      (some_none_keep S f j hlen hf havoid) (none_keep S f j hlen hf havoid)).trans
    (congrArg (embed S.diagram.toCombMap)
      (facePerm_val_self (M := S.diagram.toCombMap) (a := FaceEdgeDoubling.dart S.diagram f j)
        (b := secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
          (FaceEdgeDoubling.second S.diagram f j hlen))
        (keep := fun d => ¬ RegionInternal S.family d) (keep_alpha S.family)
        (dart_keep S f j havoid) (sigma_alpha_dart S.diagram f j hlen)
        (second_keep S f j hlen havoid)).symm))

include havoid in
/-- **(D') The dart `w` is not a crossing.** -/
theorem dart_not_phiKeep (a₀ : S.family) :
    ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1)
      ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩ := by
  rintro ⟨r, hr, s, o, h⟩
  have hrF := linkedComponentO_subset _ _ hr
  cases o with
  | false =>
    have h0 : crossO r s false = some (FaceEdgeDoubling.dart S.diagram f j) := h
    have h1 := faceOf_crossO_false r h0
    rw [FaceEdgeDoubling.dart_face] at h1
    exact (havoid r hrF).1 h1
  | true =>
    have h0 : crossO r s true = some (FaceEdgeDoubling.dart S.diagram f j) := h
    exact (havoid r hrF).2 (faceOf_crossO_false r ((crossO_alpha r s true _).mpr h0))

/-- **(F') Naming back**: `embed z` names `z`, `some none` names `w`, `none` names `alpha w`. -/
noncomputable def backCollapsed :
    (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).Dart →
      (collapsedMap S.family).Dart :=
  backDart (M := S.diagram.toCombMap) (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal (HairOpening.sectionFamily S f j hlen hf havoid).family d)
    (keep_alpha S.family) (keep_alpha (HairOpening.sectionFamily S f j hlen hf havoid).family)
    (embed_keep_iff S f j hlen hf havoid) (dart_keep S f j havoid)

/-- **(F') Face-class paths after the step name paths before it.** -/
theorem backDart_sim (a₀ : S.family)
    (x' y' : (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).Dart)
    (h : Relation.EqvGen (CombMap.FaceClassStep
      (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).dual
      (PhiKeepO (HairOpening.sectionFamily S f j hlen hf havoid).family
        (linkedComponentO (HairOpening.sectionFamily S f j hlen hf havoid).family
          ((transport S f j hlen hf havoid).map a₀)))) x' y') :
    Relation.EqvGen (CombMap.FaceClassStep (collapsedMap S.family).dual
        (PhiKeepO S.family (linkedComponentO S.family a₀.1)))
      (backCollapsed S f j hlen hf havoid x') (backCollapsed S f j hlen hf havoid y') :=
  eqvGen_backDart_of_retained (M := S.diagram.toCombMap)
    (a := FaceEdgeDoubling.dart S.diagram f j)
    (b := secondCorner S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen))
    (keep := fun d => ¬ RegionInternal S.family d)
    (keep' := fun d => ¬ RegionInternal (HairOpening.sectionFamily S f j hlen hf havoid).family d)
    (kp := PhiKeepO S.family (linkedComponentO S.family a₀.1))
    (kp' := PhiKeepO (HairOpening.sectionFamily S f j hlen hf havoid).family
      (linkedComponentO (HairOpening.sectionFamily S f j hlen hf havoid).family
        ((transport S f j hlen hf havoid).map a₀)))
    (keep_alpha S.family) (keep_alpha (HairOpening.sectionFamily S f j hlen hf havoid).family)
    (embed_keep_iff S f j hlen hf havoid) (dart_ne_second S.diagram f j hlen)
    (dart_keep S f j havoid) (sigma_alpha_dart S.diagram f j hlen)
    (second_keep S f j hlen havoid) (some_none_keep S f j hlen hf havoid)
    (none_keep S f j hlen hf havoid)
    (fun z hz => phiKeepO_map_iff (transport S f j hlen hf havoid) a₀
      (collapsedEmbed S f j hlen hf havoid) (fun _ => rfl) ⟨z, hz⟩)
    (dart_not_phiKeep S f j havoid a₀)
    (fun e => dart_not_phiKeep S f j havoid a₀
      ((phiKeepO_alpha (family := S.family) (E := linkedComponentO S.family a₀.1)
        ⟨FaceEdgeDoubling.dart S.diagram f j, dart_keep S f j havoid⟩).mp e))
    h

/-- **(F') A dart on a renumbered relator cell names a dart on the old relator cell.** -/
theorem backCollapsed_cell
    (x' : (collapsedMap (HairOpening.sectionFamily S f j hlen hf havoid).family).Dart)
    (i' : Fin (HairOpening.sectionFamily S f j hlen hf havoid).diagram.rCellCount)
    (hx : (HairOpening.sectionFamily S f j hlen hf havoid).diagram.toCombMap.faceOf x'.1 =
      (cell (HairOpening.sectionFamily S f j hlen hf havoid).diagram i').face) :
    S.diagram.toCombMap.faceOf (backCollapsed S f j hlen hf havoid x').1 =
      (cell S.diagram ((transport S f j hlen hf havoid).cellIndex.symm i')).face := by
  have hcf := cell_face_eq S.diagram f j hlen hf i'
  obtain ⟨d, _hd⟩ := x'
  cases d with
  | none =>
    exact absurd ((CellHairThickening.faceOf_none S.diagram f j hlen hf).symm.trans
      (hx.trans hcf)) (FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen _).symm
  | some d =>
    cases d with
    | none =>
      exact FaceEdgeDoubling.faceImage_injective S.diagram f j hlen
        ((faceOf_some_none_image S.diagram f j hlen hf).symm.trans (hx.trans hcf))
    | some z =>
      by_cases hz : z = FaceEdgeDoubling.dart S.diagram f j
      · subst hz
        exact absurd ((CellHairThickening.faceOf_embed_dart S.diagram f j hlen hf).symm.trans
          (hx.trans hcf)) (FaceEdgeDoubling.faceImage_ne_digon S.diagram f j hlen _).symm
      · exact FaceEdgeDoubling.faceImage_injective S.diagram f j hlen
          ((CellHairThickening.faceOf_embed S.diagram f j hlen hf hz).symm.trans (hx.trans hcf))

/-- **(G') `Φ'_M` is carried by opening a cell hair.** -/
theorem phiTransportAt_hair (a₀ : S.family) : PhiTransportAt (transport S f j hlen hf havoid) a₀ :=
  phiTransportAt_of_bypass (transport S f j hlen hf havoid) a₀
    (collapsedEmbed S f j hlen hf havoid) (fun _ => rfl) (collapsedEmbed_alpha S f j hlen hf havoid)
    (some_none_not_mem_range S f j hlen hf havoid) (dart_not_phiKeep S f j havoid a₀)
    (facePerm_w_ne S f j hlen havoid) (rotation_away S f j hlen hf havoid)
    (rotation_into S f j hlen hf havoid) (rotation_out S f j hlen hf havoid)
    (backCollapsed S f j hlen hf havoid) (fun _ => Subtype.ext rfl)
    (backDart_sim S f j hlen hf havoid a₀) (backCollapsed_cell S f j hlen hf havoid)

end Rotation

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.keep_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.sigma_alpha_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.dart_ne_second
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.faceOf_some_none_image
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.faceOf_some_none
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.face_not_mem_regionFamily
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.cell_face_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.dart_keep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.second_keep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.some_none_keep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.none_keep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.embed_keep_iff
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.facePerm_dart
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.facePerm_w_ne
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.collapsedEmbed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.collapsedEmbed_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.some_none_not_mem_range
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.rotation_away
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.rotation_into
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.rotation_out
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.dart_not_phiKeep
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.backCollapsed
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.backDart_sim
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.backCollapsed_cell
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P05CellHair.phiTransportAt_hair
