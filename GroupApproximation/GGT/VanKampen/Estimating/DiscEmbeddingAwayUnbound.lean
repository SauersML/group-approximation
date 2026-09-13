import GroupApproximation.GGT.VanKampen.SurgeryGFaceMergeRegions
import GroupApproximation.GGT.VanKampen.GFaceCornerRegionSelection
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PlanarPieces
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94InsertionTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# Section families across a corner insertion

A corner insertion into an unselected `G`-face is a `DiscEmbeddingAway` of the old diagram into
the new one.  It carries a section family (`GFaceWordInsertion.CornerOutput.retainedSection`)
and a globally distinguished section family
(`GFaceWordInsertion.CornerOutput.retainedDistinguished`) to the inserted diagram, with the same
weight and the same number of regions.  The unbound darts of a relator cell are the old ones
through the dart embedding (`DiscEmbeddingAway.sum_unboundDarts_regionFamily_card`, in
`OsinLemma94InsertionTransport`), so the unbound sum does not change
(`GFaceWordInsertion.CornerOutput.retainedDistinguished_unboundSum`).

`GloballyDistinguishedSectionFamily.insertionTransport` is the same construction for a split
corner insertion.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen.Embedded

universe u w v

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
  (originalEmbedding R).sum_unboundDarts_regionFamily_card (originalCellMap R) hcells hf S.family
    havoid

end GFaceWordInsertion.CornerOutput

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retainedDistinguished
#audit_axioms GroupApproximation.GGT.VanKampen.GFaceWordInsertion.CornerOutput.retainedDistinguished_unboundSum
