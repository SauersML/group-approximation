import GroupApproximation.GGT.VanKampen.SurgeryGCellCutIndices
import GroupApproximation.GGT.VanKampen.Estimating.ContiguityGeometryTransport

/-!
# Contiguity transport through the actual cut inclusion

The source cell and all G-region geometry return along the constructed cut
inclusion. The target may be a retained cell, a removed carrier cell, or the
original exterior. Its actual cyclic arc must have the same oriented boundary
darts as the cut region's target arc. This exact geometric identification is
the information absent from a bare `Lemma65CutData`.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- Either orientation of a target arc has its recorded number of darts. -/
theorem targetBoundaryDarts_length (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target)) :
    (targetBoundaryDarts Delta target arc).length = arc.length := by
  cases target <;> simp only [targetBoundaryDarts, CyclicArc.reverseDarts,
    List.length_map, List.length_reverse, CyclicArc.darts_length]

end GroupApproximation.GGT.VanKampen.Embedded

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells

open _root_.GroupApproximation.GGT.VanKampen.Embedded
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}
  {D : RelGenSet G Lambda} {eps : ℕ}

/-- Transport a cut contiguity to its specified ambient carrier. The actual
oriented target arc is identified as a dart list, not only by its word value. -/
noncomputable def includeContiguity (cut : RegionCutWithGCells Delta)
    {faces : Finset cut.diagram.toCombMap.Face}
    (H : ContiguityGeometry D eps cut.diagram faces)
    (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target))
    (harc : targetBoundaryDarts Delta target arc =
      (targetBoundaryDarts cut.diagram H.target H.targetArc).map cut.inclusion.darts) :
    ContiguityGeometry D eps Delta (cut.inclusion.faceSet faces) where
  boundary := cut.includeBoundary H.boundary
  source := cut.cellInclusion H.source
  target := target
  sourceArc := H.sourceArc.mapTo cut.inclusion.darts (cut.cellDarts_eq H.source)
  targetArc := arc
  rightSide := H.rightSide.map cut.inclusion.darts
  leftSide := H.leftSide.map cut.inclusion.darts
  boundary_decomposition := by
    change H.boundary.cycle.map cut.inclusion.darts = _
    rw [cut.inclusion.reverseDarts_mapTo, harc]
    exact (congrArg (List.map cut.inclusion.darts) H.boundary_decomposition).trans
      (by simp only [List.map_append])
  rightSide_length_le := by simpa only [List.length_map] using H.rightSide_length_le
  leftSide_length_le := by simpa only [List.length_map] using H.leftSide_length_le
  rightSide_norm_le := by rw [cut.inclusion.dartWord_map]; exact H.rightSide_norm_le
  leftSide_norm_le := by rw [cut.inclusion.dartWord_map]; exact H.leftSide_norm_le
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map cut.faceInclusion, cut.includeShelling H.boundary hl⟩

theorem includeContiguity_source_length (cut : RegionCutWithGCells Delta)
    {faces : Finset cut.diagram.toCombMap.Face}
    (H : ContiguityGeometry D eps cut.diagram faces)
    (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target))
    (harc : targetBoundaryDarts Delta target arc =
      (targetBoundaryDarts cut.diagram H.target H.targetArc).map cut.inclusion.darts) :
    (cut.includeContiguity H target arc harc).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length cut.inclusion.darts (cut.cellDarts_eq H.source)

theorem includeContiguity_target_length (cut : RegionCutWithGCells Delta)
    {faces : Finset cut.diagram.toCombMap.Face}
    (H : ContiguityGeometry D eps cut.diagram faces)
    (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target))
    (harc : targetBoundaryDarts Delta target arc =
      (targetBoundaryDarts cut.diagram H.target H.targetArc).map cut.inclusion.darts) :
    (cut.includeContiguity H target arc harc).targetArc.length = H.targetArc.length := by
  have h := congrArg List.length harc
  change arc.length = H.targetArc.length
  simpa only [List.length_map, targetBoundaryDarts_length] using h

/-- Transport retains the geometric contiguity degree with its original
source relator perimeter. -/
theorem includeContiguity_degree (cut : RegionCutWithGCells Delta)
    {faces : Finset cut.diagram.toCombMap.Face}
    (H : ContiguityGeometry D eps cut.diagram faces)
    (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target))
    (harc : targetBoundaryDarts Delta target arc =
      (targetBoundaryDarts cut.diagram H.target H.targetArc).map cut.inclusion.darts) :
    ((cut.includeContiguity H target arc harc).sourceArc.length : ℝ) /
        ((cell Delta (cut.includeContiguity H target arc harc).source).word.length : ℝ) =
      (H.sourceArc.length : ℝ) / ((cell cut.diagram H.source).word.length : ℝ) := by
  rw [cut.includeContiguity_source_length]
  change _ / ((cell Delta (cut.cellInclusion H.source)).word.length : ℝ) = _
  rw [← cut.cellWord_eq]

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.includeContiguity
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.includeContiguity_target_length
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.includeContiguity_degree
