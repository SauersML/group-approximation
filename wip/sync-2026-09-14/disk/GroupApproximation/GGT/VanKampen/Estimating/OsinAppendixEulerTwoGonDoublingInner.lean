import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixEulerTwoGonDoublingInnerSupport
import GroupApproximation.Meta.AxiomGuard

/-!
# A clean two-gon through a cell side doubling

Osin, arXiv:math/0411039v3, Appendix, the assumption before Lemma 9.3: "inside every 2-gon of
`Φ′_M`, there is a vertex of `Φ_M`".

`TwoGonCellSideStepStatement` (`Estimating/OsinAppendixEulerTwoGonDoublingTransport`): one doubling
`CellSideThickening.sectionFamilyOfArcs` along a dart `w_j` of an inner face `f` that no region
contains, with `w_j` on no arc, keeps a clean two-gon.
* Every region is carried with its face set and arcs through the dart embedding, and cells are
  renumbered by `FaceEdgeDoubling.cellMap` (`cellSideTransport`).
* The doubling is an edge insertion at `w_j` and `σ (α w_j)`; both new darts, `w_j` and the corner
  lie in the collapsed maps, and the face rotation of the new collapsed map detours through
  `some none` in place of `w_j`, which is not a crossing.  So `Φ'_M` is carried, and face-class paths
  name paths before the doubling (`cellSide_phiTransportAt`).

* `PhiMapTransport.cellSideTransport`, `cellSide_phiTransportAt`.
* `PhiMapTransport.twoGonCellSideStep : TwoGonCellSideStepStatement`.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121,
`\begin{theorem}[Hull's small cancellation theorem]\label{thm:hull}`), through Osin's Lemma 9.7(a);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.PhiMapTransport

open Equiv Embedded Embedded.RegionCandidate EdgeInsertion

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **The regions of a cell side doubling**, carried along their arcs. -/
noncomputable def cellSideTransport (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family) :
    RegionTransport S (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid) where
  map := FaceEdgeDoubling.regionFamilyOfArcsEmbedding S.diagram f j hlen hf S.family havoid
  family_eq := rfl
  cellIndex := (FaceEdgeDoubling.cellMap S.diagram f j hlen hf).indexEquiv
  source _ := rfl
  target _ := rfl
  profile a := FaceEdgeDoubling.regionCandidateOfArcs_profile S.diagram f j hlen hf
    ⟨a.1, havoid a.1 a.2⟩
  darts := (FaceEdgeDoubling.embedding S.diagram f j hlen hf).darts
  cross a s o := crossO_map_of_arcs (FaceEdgeDoubling.embedding S.diagram f j hlen hf).darts
    (fun d => (FaceEdgeDoubling.embedding S.diagram f j hlen hf).alpha d)
    (FaceEdgeDoubling.mapTo_darts_of_avoid S.diagram f j hlen hf a.1.2.sourceArc _
      (fun _ hd => FaceEdgeDoubling.carrierImage_of_ne_dart S.diagram f j hlen hf _ hd) _
      (havoid a.1 a.2).2.1)
    (FaceEdgeDoubling.mapTo_darts_of_avoid S.diagram f j hlen hf a.1.2.targetArc _
      (fun _ hd => FaceEdgeDoubling.targetImage_of_ne_dart S.diagram f j hlen hf _ hd) _
      (havoid a.1 a.2).2.2)
    Option.map_eq_none_iff s o

/-- **`Φ'_M` is carried by a cell side doubling.** -/
theorem cellSide_phiTransportAt (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    (f : S.diagram.toCombMap.Face) (j : Fin (S.diagram.faceBoundary f).darts.length)
    (hlen : 1 < (S.diagram.faceBoundary f).darts.length) (hf : f ≠ S.diagram.outerFace)
    (havoid : FaceEdgeDoubling.FamilyArcAvoid S.diagram f j S.family) (a₀ : S.family) :
    PhiTransportAt (cellSideTransport S f j hlen hf havoid) a₀ := by
  classical
  have hF : ∀ a ∈ S.family, f ∉ a.1 := fun a ha => (havoid a ha).1
  have hint := regionInternal_embed_iff S.diagram f j hlen hf hF
    (FaceEdgeDoubling.regionFamilyOfArcsEmbedding S.diagram f j hlen hf S.family havoid)
    (fun _ => rfl)
  obtain ⟨hsn, hn⟩ := not_regionInternal_new S.diagram f j hlen hf hF
    (FaceEdgeDoubling.regionFamilyOfArcsEmbedding S.diagram f j hlen hf S.family havoid)
    (fun _ => rfl)
  have hkeep : ∀ d, ¬ RegionInternal S.family (S.diagram.toCombMap.alpha d) ↔
      ¬ RegionInternal S.family d := fun d => not_congr (regionInternal_alpha _ d)
  have hkeep' : ∀ d, ¬ RegionInternal (CellSideThickening.sectionFamilyOfArcs S f j hlen hf
      havoid).family ((FaceEdgeDoubling.map S.diagram f j hlen).alpha d) ↔
        ¬ RegionInternal (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family d :=
    fun d => not_congr (regionInternal_alpha _ d)
  have hembed : ∀ z, ¬ RegionInternal (CellSideThickening.sectionFamilyOfArcs S f j hlen hf
      havoid).family (embed S.diagram.toCombMap z) ↔ ¬ RegionInternal S.family z :=
    fun z => not_congr (hint z)
  have hoff : ∀ {z}, S.diagram.toCombMap.faceOf z = f → ¬ RegionInternal S.family z :=
    fun hz ⟨a, ha, h1, -⟩ => hF a ha (hz ▸ h1)
  have hwk : ¬ RegionInternal S.family (FaceEdgeDoubling.dart S.diagram f j) :=
    hoff (FaceEdgeDoubling.dart_face S.diagram f j)
  have hbk : ¬ RegionInternal S.family (EnclosedBridgeDoubling.corner S.diagram f j hlen) :=
    hoff ((corners_face_eq S.diagram.toCombMap (FaceEdgeDoubling.rebased S.diagram f j)
      (FaceEdgeDoubling.second S.diagram f j hlen)).symm.trans
        (FaceEdgeDoubling.dart_face S.diagram f j))
  have hab := EnclosedBridgeDoubling.corner_ne S.diagram f j hlen
  have hba := EnclosedBridgeDoubling.sigma_alpha_dart S.diagram f j hlen
  let ιc : (collapsedMap S.family).Dart ↪
      (collapsedMap (CellSideThickening.sectionFamilyOfArcs S f j hlen hf havoid).family).Dart :=
    ⟨fun x => ⟨embed S.diagram.toCombMap x.1, (hembed x.1).mpr x.2⟩,
      fun x y h => Subtype.ext (embed_injective _ (congrArg Subtype.val h))⟩
  have hw : ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1)
      ⟨FaceEdgeDoubling.dart S.diagram f j, hwk⟩ := by
    rintro ⟨a, ha, s, o, h⟩
    have hav := havoid a (linkedComponentO_subset _ _ ha)
    refine crossO_ne_of_arcs hav.2.1 hav.2.2 ?_ ?_ s o h
    · rw [FaceEdgeDoubling.dart_face]
      exact hav.1
    · rw [FaceEdgeDoubling.dart_face]
      exact hf
  have hkaa : ¬ PhiKeepO S.family (linkedComponentO S.family a₀.1)
      ⟨S.diagram.toCombMap.alpha (FaceEdgeDoubling.dart S.diagram f j), (hkeep _).mpr hwk⟩ :=
    fun h => hw ((phiKeepO_alpha ⟨FaceEdgeDoubling.dart S.diagram f j, hwk⟩).mp h)
  refine phiTransportAt_of_bypass (cellSideTransport S f j hlen hf havoid) a₀ ιc (fun _ => rfl)
    (fun _ => Subtype.ext rfl) (w := ⟨FaceEdgeDoubling.dart S.diagram f j, hwk⟩)
    (s := ⟨some none, hsn⟩) ?_ hw ?_ ?_ ?_ ?_ (backDart hkeep hkeep' hembed hwk) (fun _ => rfl)
    (fun _ _ h => eqvGen_backDart_of_retained hkeep hkeep' hembed hab hwk hba hbk hsn hn
      (fun z hz => phiKeepO_map_iff (cellSideTransport S f j hlen hf havoid) a₀ ιc (fun _ => rfl)
        ⟨z, hz⟩) hw hkaa h)
    (fun x' i' h => faceOf_backDart_eq_cell S.diagram f j hlen hf hkeep hkeep' hembed hwk x' i' h)
  · rintro ⟨x, hx⟩
    exact Option.noConfusion (congrArg Subtype.val hx)
  · intro h
    exact hab ((congrArg Subtype.val h).symm.trans (facePerm_val_self hkeep hwk hba hbk))
  · intro x hxw hfx
    have hne : x.1 ≠ FaceEdgeDoubling.dart S.diagram f j := fun h => hxw (Subtype.ext h)
    have hval := facePerm_val_of_retained hkeep hkeep' hembed hab hwk hba hsn x.2 hne
    rw [if_neg (fun h => hfx (Subtype.ext h))] at hval
    exact Subtype.ext hval
  · intro x hxw hfx
    have hne : x.1 ≠ FaceEdgeDoubling.dart S.diagram f j := fun h => hxw (Subtype.ext h)
    have hval := facePerm_val_of_retained hkeep hkeep' hembed hab hwk hba hsn x.2 hne
    rw [if_pos (congrArg Subtype.val hfx)] at hval
    exact Subtype.ext hval
  · exact Subtype.ext ((facePerm_val_some_none hkeep' hembed hbk hsn hn).trans
      (congrArg (embed S.diagram.toCombMap) (facePerm_val_self hkeep hwk hba hbk).symm))

/-- **A clean two-gon through a cell side doubling.** -/
theorem twoGonCellSideStep : TwoGonCellSideStepStatement.{u, w, v} := by
  intro G _ Lambda W D lambda c eps Delta cuts hlea S f j hlen hf havoid h
  exact hasCleanTwoGon_of_transport hlea (cellSideTransport S f j hlen hf havoid)
    (cellSide_phiTransportAt S f j hlen hf havoid) h

end GroupApproximation.GGT.VanKampen.PhiMapTransport

#audit_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.cellSide_phiTransportAt
#audit_closed_axioms GroupApproximation.GGT.VanKampen.PhiMapTransport.twoGonCellSideStep
