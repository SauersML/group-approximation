import GroupApproximation.GGT.VanKampen.Estimating.ContiguityTransport
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometry

/-!
# Retain contiguity geometry, including self-contiguities, through insertion

The same actual boundary and shelling transport retains arcs, sides and
metric bounds. The cell-index bijection preserves and reflects self-targets.
No distinct-cell O52 certificate is needed for the geometric operation.
-/

namespace GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

open Embedded
universe u w v v'
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W} {Xi : DiscDiagram.{u, w, v'} W}
  {f : Delta.toCombMap.Face} (E : DiscEmbeddingAway Delta Xi f)
  (C : Surgery.OrderedRCellMap Delta Xi E.faces)
  (hcells : ∀ cell ∈ Delta.relatorCells, cell.face ≠ f)
  (hf : f ≠ Delta.outerFace)

/-- Transport the actual geometry without a distinct-cell or O52 premise. -/
def contiguityGeometry {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (H : ContiguityGeometry D eps Delta s) : ContiguityGeometry D eps Xi (E.faceSet s) where
  boundary := E.boundary s hs H.boundary
  source := C.indexEquiv H.source
  target := H.target.map C.indexEquiv
  sourceArc := H.sourceArc.mapTo E.darts (E.cellDarts_eq C hcells H.source)
  targetArc := H.targetArc.mapTo E.darts (E.targetDarts_eq C hcells hf H.target)
  rightSide := H.rightSide.map E.darts
  leftSide := H.leftSide.map E.darts
  boundary_decomposition := by
    change H.boundary.cycle.map E.darts = _
    rw [E.reverseDarts_mapTo, E.targetBoundaryDarts_map C hcells hf]
    exact (congrArg (List.map E.darts) H.boundary_decomposition).trans
      (by simp only [List.map_append])
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by rw [E.dartWord_map]; exact H.rightSide_norm_le
  leftSide_norm_le := by rw [E.dartWord_map]; exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map E.faces, E.shelling s hs hl⟩

theorem contiguityGeometry_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s) (H : ContiguityGeometry D eps Delta s) :
    (E.contiguityGeometry C hcells hf hs H).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length E.darts (E.cellDarts_eq C hcells H.source)

theorem contiguityGeometry_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s) (H : ContiguityGeometry D eps Delta s) :
    (E.contiguityGeometry C hcells hf hs H).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length E.darts (E.targetDarts_eq C hcells hf H.target)

/-- An actual self-target is retained and reflected by the cell-index map. -/
theorem contiguityGeometry_self_target_iff {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s) (H : ContiguityGeometry D eps Delta s) :
    (E.contiguityGeometry C hcells hf hs H).target =
        some (E.contiguityGeometry C hcells hf hs H).source ↔
      H.target = some H.source := by
  change (Equiv.optionCongr C.indexEquiv) H.target =
    (Equiv.optionCongr C.indexEquiv) (some H.source) ↔ _
  exact (Equiv.optionCongr C.indexEquiv).injective.eq_iff

end GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.contiguityGeometry
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.contiguityGeometry_source_length
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.contiguityGeometry_target_length
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.contiguityGeometry_self_target_iff
