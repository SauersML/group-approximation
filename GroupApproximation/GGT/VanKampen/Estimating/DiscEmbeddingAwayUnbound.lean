import GroupApproximation.GGT.VanKampen.SurgeryGFaceMergeRegions
import GroupApproximation.GGT.VanKampen.GFaceCornerRegionSelection
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Unbound darts through an embedding away from a face

A `DiscEmbeddingAway Delta Xi f` carries a compatible family of region candidates avoiding `f`
to a family on `Xi` (`DiscEmbeddingAway.regionFamily`).  The relator cells of `Xi` are those of
`Delta`, reindexed by the ordered cell map, and their darts are the old ones through `darts`.
A dart of a relator cell of `Xi` is used by a transported region exactly when its old dart was
used by the old region, so the unbound darts of every relator cell correspond through `darts`
(`DiscEmbeddingAway.unboundDarts_eq`) and their total number is unchanged
(`DiscEmbeddingAway.sum_unboundDarts_card`).

A corner insertion into an unselected `G`-face is such an embedding.  It carries a section
family (`GFaceWordInsertion.CornerOutput.retainedSection`) and a globally distinguished section
family (`GFaceWordInsertion.CornerOutput.retainedDistinguished`) to the inserted diagram, with
the same weight, the same number of regions and the same unbound sum
(`GFaceWordInsertion.CornerOutput.retainedDistinguished_unboundSum`).
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded

universe u w v v'

namespace DiscEmbeddingAway

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {f : Delta.toCombMap.Face} (E : DiscEmbeddingAway Delta Xi f)
  (C : Surgery.OrderedRCellMap Delta Xi E.faces)
  (hcells : ∀ cell ∈ Delta.relatorCells, cell.face ≠ f) (hf : f ≠ Delta.outerFace)

theorem regionCandidate_source_eq_iff (a : { a : RegionCandidate D eps Delta // f ∉ a.1 })
    (i : Fin Delta.rCellCount) :
    (E.regionCandidate C hcells hf a).2.source = C.indexEquiv i ↔ a.val.2.source = i :=
  C.indexEquiv.apply_eq_iff_eq

theorem regionCandidate_target_eq_some_iff
    (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) (i : Fin Delta.rCellCount) :
    (E.regionCandidate C hcells hf a).2.target = some (C.indexEquiv i) ↔
      a.val.2.target = some i := by
  change Option.map C.indexEquiv a.val.2.target = some (C.indexEquiv i) ↔ _
  constructor
  · intro h
    exact Option.map_injective C.indexEquiv.injective h
  · intro h
    rw [h]
    rfl

theorem regionCandidate_target_isSome (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) :
    (E.regionCandidate C hcells hf a).2.target.isSome = a.val.2.target.isSome :=
  Option.isSome_map

theorem regionCandidate_sourceArc_darts (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) :
    (E.regionCandidate C hcells hf a).2.sourceArc.darts = a.val.2.sourceArc.darts.map E.darts :=
  CyclicArc.mapTo_darts a.val.2.sourceArc E.darts (E.cellDarts_eq C hcells a.val.2.source)

theorem regionCandidate_targetArc_darts (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) :
    (E.regionCandidate C hcells hf a).2.targetArc.darts = a.val.2.targetArc.darts.map E.darts :=
  CyclicArc.mapTo_darts a.val.2.targetArc E.darts (E.targetDarts_eq C hcells hf a.val.2.target)

theorem mem_cellArcDarts_regionCandidate_iff
    (a : { a : RegionCandidate D eps Delta // f ∉ a.1 }) (i : Fin Delta.rCellCount)
    (d : Delta.toCombMap.Dart) :
    E.darts d ∈ (E.regionCandidate C hcells hf a).cellArcDarts (C.indexEquiv i) ↔
      d ∈ a.val.cellArcDarts i := by
  rw [Surgery.GFaceMerge.mem_cellArcDarts_iff, Surgery.GFaceMerge.mem_cellArcDarts_iff,
    E.regionCandidate_source_eq_iff C hcells hf, E.regionCandidate_target_eq_some_iff C hcells hf,
    E.regionCandidate_sourceArc_darts C hcells hf, E.regionCandidate_targetArc_darts C hcells hf,
    List.mem_map_of_injective E.darts.injective, List.mem_map_of_injective E.darts.injective]

/-- A dart of a relator cell of `Xi` is used by a transported region of either kind exactly
when its old dart was used by the old region. -/
theorem mem_boundDarts_regionFamily_iff (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) (interior : Bool) (i : Fin Delta.rCellCount)
    (d : Delta.toCombMap.Dart) :
    E.darts d ∈ RegionCandidate.boundDarts (E.regionFamily C hcells hf family havoid) interior
        (C.indexEquiv i) ↔
      d ∈ RegionCandidate.boundDarts family interior i := by
  rw [Surgery.GFaceMerge.mem_boundDarts_iff, Surgery.GFaceMerge.mem_boundDarts_iff]
  constructor
  · rintro ⟨a', ha', hkind, hd⟩
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp ha'
    exact ⟨b.val, b.property,
      (E.regionCandidate_target_isSome C hcells hf ⟨b.val, havoid b.val b.property⟩).symm.trans
        hkind,
      (E.mem_cellArcDarts_regionCandidate_iff C hcells hf ⟨b.val, havoid b.val b.property⟩ i
        d).mp hd⟩
  · rintro ⟨b, hb, hkind, hd⟩
    exact ⟨E.regionCandidate C hcells hf ⟨b, havoid b hb⟩,
      Finset.mem_map.mpr ⟨⟨b, hb⟩, Finset.mem_attach _ _, rfl⟩,
      (E.regionCandidate_target_isSome C hcells hf ⟨b, havoid b hb⟩).trans hkind,
      (E.mem_cellArcDarts_regionCandidate_iff C hcells hf ⟨b, havoid b hb⟩ i d).mpr hd⟩

/-- **A dart of a relator cell of `Xi` is unbound exactly when its old dart was.** -/
theorem mem_unboundDarts_regionFamily_iff (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) (i : Fin Delta.rCellCount) (d : Delta.toCombMap.Dart) :
    E.darts d ∈ RegionCandidate.unboundDarts (E.regionFamily C hcells hf family havoid)
        (C.indexEquiv i) ↔
      d ∈ RegionCandidate.unboundDarts family i := by
  rw [Surgery.GFaceMerge.mem_unboundDarts_iff, Surgery.GFaceMerge.mem_unboundDarts_iff,
    E.cellDarts_eq C hcells i, List.mem_map_of_injective E.darts.injective,
    E.mem_boundDarts_regionFamily_iff C hcells hf family havoid false i d,
    E.mem_boundDarts_regionFamily_iff C hcells hf family havoid true i d]

/-- **The unbound darts of a relator cell are the old ones, through `darts`.** -/
theorem unboundDarts_eq (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) (i : Fin Delta.rCellCount) :
    RegionCandidate.unboundDarts (E.regionFamily C hcells hf family havoid) (C.indexEquiv i) =
      (RegionCandidate.unboundDarts family i).map E.darts := by
  ext x
  rw [Finset.mem_map]
  constructor
  · intro hx
    have hcell := ((Surgery.GFaceMerge.mem_unboundDarts_iff _ _ x).mp hx).1
    rw [E.cellDarts_eq C hcells i] at hcell
    obtain ⟨d, -, rfl⟩ := List.mem_map.mp hcell
    exact ⟨d, (E.mem_unboundDarts_regionFamily_iff C hcells hf family havoid i d).mp hx, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact (E.mem_unboundDarts_regionFamily_iff C hcells hf family havoid i d).mpr hd

theorem unboundDarts_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) (i : Fin Delta.rCellCount) :
    (RegionCandidate.unboundDarts (E.regionFamily C hcells hf family havoid)
        (C.indexEquiv i)).card =
      (RegionCandidate.unboundDarts family i).card := by
  rw [E.unboundDarts_eq C hcells hf family havoid i, Finset.card_map]

/-- **The total unbound length is unchanged.** -/
theorem sum_unboundDarts_card (family : Finset (RegionCandidate D eps Delta))
    (havoid : ∀ a ∈ family, f ∉ a.1) :
    ∑ j : Fin Xi.rCellCount,
        (RegionCandidate.unboundDarts (E.regionFamily C hcells hf family havoid) j).card =
      ∑ i : Fin Delta.rCellCount, (RegionCandidate.unboundDarts family i).card := by
  rw [← Equiv.sum_comp C.indexEquiv]
  exact Finset.sum_congr rfl fun i _ => E.unboundDarts_card C hcells hf family havoid i

end DiscEmbeddingAway

namespace GFaceWordInsertion.CornerOutput

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}

/-- **A section family across a corner insertion into a face it avoids.** -/
noncomputable def retainedSection {alphabet : RelGenSet G Lambda}
    (S : RealizedSectionFamily D lambda c eps Delta cuts)
    {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
    {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
    {start finish : Fin (S.diagram.faceBoundary f).darts.length}
    {word : List (RelLetter G Lambda)}
    (R : CornerOutput alphabet S.diagram f hf hcells start finish word)
    (havoid : ∀ a ∈ S.family, f ∉ a.1) :
    RealizedSectionFamily D lambda c eps Delta cuts where
  toRealizedRegionFamily := retainedRegionRealization (S := S.toRealizedRegionFamily) R havoid
  respects := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := (originalEmbedding R).regionFamily_profile (originalCellMap R)
      hcells hf S.family havoid ha
    exact RegionCandidate.respectsSections_of_sameTargetProfile cuts hab (S.respects b hb)
  nondegenerate := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := (originalEmbedding R).regionFamily_profile (originalCellMap R)
      hcells hf S.family havoid ha
    obtain ⟨hs, ht⟩ := S.nondegenerate b hb
    exact ⟨lt_of_lt_of_eq hs hab.2.2.2.symm, lt_of_lt_of_eq ht hab.2.2.1.symm⟩

/-- **A distinguished section family across a corner insertion into a face it avoids.**  The
insertion keeps the weight and the number of regions, and its labels are legal, so the
transported family is again optimal. -/
noncomputable def retainedDistinguished
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
    {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
    {start finish : Fin (S.diagram.faceBoundary f).darts.length}
    {word : List (RelLetter G Lambda)}
    (R : CornerOutput (symmetricLabelAlphabet D) S.diagram f hf hcells start finish word)
    (havoid : ∀ a ∈ S.family, f ∉ a.1) :
    GloballyDistinguishedSectionFamily D lambda c eps Delta cuts where
  toRealizedSectionFamily := retainedSection S.toRealizedSectionFamily R havoid
  label_admissible := retainedRegion_legal (S := S.toRealizedRegionFamily) R havoid
  weight_maximal other hother :=
    (S.weight_maximal other hother).trans_eq
      (retainedRegion_weight (S := S.toRealizedRegionFamily) R havoid).symm
  card_minimal other hother hweight :=
    (retainedRegion_card (S := S.toRealizedRegionFamily) R havoid).trans_le
      (S.card_minimal other hother
        (hweight.trans (retainedRegion_weight (S := S.toRealizedRegionFamily) R havoid)))

theorem retainedDistinguished_diagram
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
    {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
    {start finish : Fin (S.diagram.faceBoundary f).darts.length}
    {word : List (RelLetter G Lambda)}
    (R : CornerOutput (symmetricLabelAlphabet D) S.diagram f hf hcells start finish word)
    (havoid : ∀ a ∈ S.family, f ∉ a.1) :
    (retainedDistinguished S R havoid).diagram = R.diagram :=
  rfl

theorem retainedDistinguished_family
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
    {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
    {start finish : Fin (S.diagram.faceBoundary f).darts.length}
    {word : List (RelLetter G Lambda)}
    (R : CornerOutput (symmetricLabelAlphabet D) S.diagram f hf hcells start finish word)
    (havoid : ∀ a ∈ S.family, f ∉ a.1) :
    (retainedDistinguished S R havoid).family =
      (originalEmbedding R).regionFamily (originalCellMap R) hcells hf S.family havoid :=
  rfl

/-- **The unbound sum is unchanged.** -/
theorem retainedDistinguished_unboundSum
    (S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts)
    {f : S.diagram.toCombMap.Face} {hf : f ≠ S.diagram.outerFace}
    {hcells : ∀ C ∈ S.diagram.relatorCells, C.face ≠ f}
    {start finish : Fin (S.diagram.faceBoundary f).darts.length}
    {word : List (RelLetter G Lambda)}
    (R : CornerOutput (symmetricLabelAlphabet D) S.diagram f hf hcells start finish word)
    (havoid : ∀ a ∈ S.family, f ∉ a.1) :
    (retainedDistinguished S R havoid).unboundSum = S.unboundSum :=
  (originalEmbedding R).sum_unboundDarts_card (originalCellMap R) hcells hf S.family havoid

end GFaceWordInsertion.CornerOutput

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.unboundDarts_eq
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.sum_unboundDarts_card
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retainedDistinguished
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retainedDistinguished_unboundSum
