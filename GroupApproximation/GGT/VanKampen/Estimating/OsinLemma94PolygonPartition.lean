import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonMaximal
import GroupApproximation.Meta.AxiomGuard

/-!
# The polygon partition of Osin's Lemma 9.4

`OsinLemma94PolygonPartitionInput` (in `OsinLemma94PolygonRealization.lean`) asks, for a
globally distinguished section family with `1 ≤ ε` whose G-faces are apart and whose cell arcs,
boundary arcs and cutting chains are quasi-geodesic, for a realization of the unselected G-faces
as polygons with maximal sides.  This module proves it (`osinLemma94PolygonPartitionInput`).

* The polygons are the unselected G-faces, enumerated (`polygonFace`).
* The sides of a polygon are `sidesOf` (`OsinLemma94PolygonKinds.lean`): the walk of the face,
  read from its base, cut into maximal runs of one kind, with short runs cut into chunks of
  length at most `ε`.
* The side facts are in `OsinLemma94PolygonSides.lean`, and maximality is in
  `OsinLemma94PolygonMaximal.lean`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace GloballyDistinguishedSectionFamily

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)

open Classical in
/-- The unselected G-faces form a finite type. -/
@[reducible] noncomputable def polygonFaces :
    Fintype {f : S.diagram.toCombMap.Face // S.UnselectedGFace f} :=
  Subtype.fintype _

/-- The number of unselected G-faces. -/
noncomputable def polygonCount : ℕ := @Fintype.card _ S.polygonFaces

/-- The unselected G-faces, enumerated. -/
noncomputable def polygonFace (k : Fin S.polygonCount) : S.diagram.toCombMap.Face :=
  ((@Fintype.equivFin _ S.polygonFaces).symm k).1

theorem polygonFace_unselected (k : Fin S.polygonCount) :
    S.UnselectedGFace (S.polygonFace k) :=
  ((@Fintype.equivFin _ S.polygonFaces).symm k).2

theorem polygonFace_injective : Function.Injective S.polygonFace := fun _ _ h =>
  (@Fintype.equivFin _ S.polygonFaces).symm.injective (Subtype.ext h)

theorem exists_polygonFace {f : S.diagram.toCombMap.Face} (hf : S.UnselectedGFace f) :
    ∃ k, S.polygonFace k = f :=
  ⟨@Fintype.equivFin _ S.polygonFaces ⟨f, hf⟩, by rw [polygonFace, Equiv.symm_apply_apply]⟩

/-- A face other than the outer face, not the face of an indexed cell and in no selected region,
is an unselected G-face. -/
theorem unselectedGFace_of_cells {f : S.diagram.toCombMap.Face}
    (h₁ : f ≠ S.diagram.outerFace)
    (h₂ : ∀ j : Fin S.diagram.rCellCount, (Embedded.cell S.diagram j).face ≠ f)
    (h₃ : ∀ a ∈ S.family, f ∉ a.1) : S.UnselectedGFace f := by
  unfold UnselectedGFace
  refine ⟨h₁, fun C hC => ?_, h₃⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hC
  exact h₂ ⟨i, hi⟩

theorem getD_mem_sidesOf {f : S.diagram.toCombMap.Face} {i : ℕ}
    (hi : i < (S.sidesOf f).length) : (S.sidesOf f).getD i [] ∈ S.sidesOf f := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem nodup_of_mem_sidesOf (heps : 1 ≤ eps) {f : S.diagram.toCombMap.Face}
    {m : List S.diagram.toCombMap.Dart} (hm : m ∈ S.sidesOf f) : m.Nodup :=
  (List.nodup_rotate.mpr (S.diagram.faceBoundary f).nodup).sublist
    (S.side_facts heps hm).2.1.sublist

/-- A cutting side runs back across itself. -/
theorem runsBackAcross_of_side {m : List S.diagram.toCombMap.Dart}
    (hm : m.IsChain S.SameSide) (hkind : S.sideKind m = .cutting) : S.RunsBackAcross m :=
  S.runsBackAcross_of_isChain
    (S.backChain_of_side hm (by rw [hkind]; nofun) fun _ => by rw [hkind]; nofun)

/-- **The polygons of Lemma 9.4.**  The unselected G-faces, each with its walk cut into the
sides `sidesOf`. -/
noncomputable def realizedPolygons (heps : 1 ≤ eps) (hapart : S.GFacesApart)
    (hcell : S.CellArcsQuasiGeodesic) (hbd : S.BoundaryArcsQuasiGeodesic)
    (hcut : S.CuttingChainsQuasiGeodesic) : OsinLemma94RealizedPolygons S where
  count := S.polygonCount
  face := S.polygonFace
  face_injective := S.polygonFace_injective
  face_ne_outer := fun k => (S.polygonFace_unselected k).1
  face_not_cell := fun k j => (S.polygonFace_unselected k).2.1 _ (Embedded.cell_mem S.diagram j)
  face_unselected := fun k => (S.polygonFace_unselected k).2.2
  face_complete := fun _ h₁ h₂ h₃ => S.exists_polygonFace (S.unselectedGFace_of_cells h₁ h₂ h₃)
  sideCount := fun k => (S.sidesOf (S.polygonFace k)).length
  sideDarts := fun k i => (S.sidesOf (S.polygonFace k)).getD i []
  base := fun k => S.baseOf (S.polygonFace k)
  walk := fun k => (S.flatten_sidesOf (S.polygonFace k)).symm.trans
    ((PolygonList.range_flatMap_getD (S.sidesOf (S.polygonFace k)) id).trans List.flatMap_id).symm
  side_ne_nil := fun _ _ hi => (S.side_facts heps (S.getD_mem_sidesOf hi)).1
  kind := fun k i => S.sideKind ((S.sidesOf (S.polygonFace k)).getD i [])
  cell_arc := fun _ _ _ hi hkind =>
    S.cell_arc_of_side (S.side_facts heps (S.getD_mem_sidesOf hi)).2.2.1
      (S.nodup_of_mem_sidesOf heps (S.getD_mem_sidesOf hi)) hkind
  boundary_arc := fun _ _ _ hi hkind =>
    S.boundary_arc_of_side (S.side_facts heps (S.getD_mem_sidesOf hi)).2.2.1
      (S.side_facts heps (S.getD_mem_sidesOf hi)).1 hkind
  cutting_internal := fun k _ hi hkind =>
    S.cutting_internal_of_side hapart (S.polygonFace_unselected k)
      (S.side_facts heps (S.getD_mem_sidesOf hi)).2.2.1
      (fun _ hd => S.face_of_mem_rotate ((S.side_facts heps (S.getD_mem_sidesOf hi)).2.1.subset hd))
      hkind
  cutting_interior := fun _ _ hi hkind =>
    S.runsBackAcross_of_side (S.side_facts heps (S.getD_mem_sidesOf hi)).2.2.1 hkind
  short_region := fun _ _ hi hkind =>
    S.short_region_of_side (S.side_facts heps (S.getD_mem_sidesOf hi)).2.2.1
      (S.side_facts heps (S.getD_mem_sidesOf hi)).1 hkind
  closed := fun k => S.listVal_sidesOf (S.polygonFace_unselected k)
  quasiGeodesic := fun k _ hi hkind =>
    S.quasiGeodesic_of_side hapart hcell hbd hcut (S.polygonFace_unselected k)
      (S.side_facts heps (S.getD_mem_sidesOf hi)).2.2.1
      (S.side_facts heps (S.getD_mem_sidesOf hi)).1
      (S.side_facts heps (S.getD_mem_sidesOf hi)).2.1 hkind
  short := fun _ _ hi hkind =>
    S.short_of_side ((S.side_facts heps (S.getD_mem_sidesOf hi)).2.2.2 hkind)

/-- The sides of the polygons are maximal. -/
theorem realizedPolygons_maximal (heps : 1 ≤ eps) (hapart : S.GFacesApart)
    (hcell : S.CellArcsQuasiGeodesic) (hbd : S.BoundaryArcsQuasiGeodesic)
    (hcut : S.CuttingChainsQuasiGeodesic) :
    (S.realizedPolygons heps hapart hcell hbd hcut).Maximal := by
  intro k i hi hkind
  exact S.sidesOf_maximal heps (S.polygonFace k) i hi hkind

#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.exists_polygonFace
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.unselectedGFace_of_cells
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.realizedPolygons
#audit_axioms GroupApproximation.GGT.VanKampen.GloballyDistinguishedSectionFamily.realizedPolygons_maximal

end GloballyDistinguishedSectionFamily

/-- **The polygon partition of Lemma 9.4 holds.**  The unselected G-faces, with their walks cut
into `sidesOf`, are polygons with maximal sides. -/
theorem osinLemma94PolygonPartitionInput : OsinLemma94PolygonPartitionInput.{u, w, v} := by
  intro _ _ _ _ _ _ _ _ _ _ S heps hapart hcell hbd hcut
  exact ⟨S.realizedPolygons heps hapart hcell hbd hcut,
    S.realizedPolygons_maximal heps hapart hcell hbd hcut⟩

#audit_closed_axioms GroupApproximation.GGT.VanKampen.osinLemma94PolygonPartitionInput

end GroupApproximation.GGT.VanKampen
