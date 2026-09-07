import GroupApproximation.GGT.VanKampen.SurgeryGCellCutDiagram
import GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

/-!
# The actual inclusion of a cut into its source

The cut retains a subtype of source darts. Every inner face is an unchanged
source face; only the cut exterior is new. This constructs the geometric
embedding away from that exterior, rather than asking a cut consumer to
recover it from a cell-count inequality or boundary-word equality.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

universe u w v

private def keptOrOuterEmbedding (M : CombMap.{v}) (outside : Finset M.Face)
    (outer : M.Face) (houter : outer ∈ outside) :
    ({f : M.Face // f ∉ outside} ⊕ PUnit.{v + 1}) ↪ M.Face where
  toFun := Sum.elim Subtype.val (fun _ => outer)
  inj' := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext hxy)
      | inr y =>
        change x.1 = outer at hxy
        exact (x.2 (hxy.symm ▸ houter)).elim
    | inr x =>
      cases y with
      | inl y =>
        change outer = y.1 at hxy
        exact (y.2 (hxy ▸ houter)).elim
      | inr y => exact congrArg Sum.inr (Subsingleton.elim x y)

namespace RegionCutWithGCells

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- Inner faces return to their original source faces. The exceptional new
exterior maps to the old exterior solely to complete the face injection. -/
noncomputable def faceInclusion (cut : RegionCutWithGCells Delta) :
    cut.diagram.toCombMap.Face ↪ Delta.toCombMap.Face :=
  (replaceGRegionFaceEquiv Delta.toCombMap cut.outside cut.region).toEmbedding.trans
    (keptOrOuterEmbedding Delta.toCombMap cut.outside Delta.outerFace cut.outer_mem)

theorem faceInclusion_kept (cut : RegionCutWithGCells Delta)
    (f : Delta.toCombMap.Face) (hf : f ∉ cut.outside) :
    cut.faceInclusion (keptFace Delta.toCombMap cut.outside cut.region f hf) = f := by
  change Sum.elim Subtype.val (fun _ => Delta.outerFace)
    (replaceGRegionFaceEquiv Delta.toCombMap cut.outside cut.region
      ((replaceGRegionFaceEquiv Delta.toCombMap cut.outside cut.region).symm
        (Sum.inl ⟨f, hf⟩))) = f
  rw [Equiv.apply_symm_apply]
  rfl

theorem faceInclusion_outer (cut : RegionCutWithGCells Delta) :
    cut.faceInclusion cut.diagram.outerFace = Delta.outerFace := by
  change Sum.elim Subtype.val (fun _ => Delta.outerFace)
    (replaceGRegionFaceEquiv Delta.toCombMap cut.outside cut.region
      ((replaceGRegionFaceEquiv Delta.toCombMap cut.outside cut.region).symm
        (Sum.inr PUnit.unit))) = Delta.outerFace
  rw [Equiv.apply_symm_apply]
  rfl

/-- All retained dart labels, reversals and inner face boundaries are the
source data. The exceptional exterior is not asserted to retain its word. -/
noncomputable def inclusion (cut : RegionCutWithGCells Delta) :
    DiscEmbeddingAway cut.diagram Delta cut.diagram.outerFace where
  darts := Function.Embedding.subtype _
  faces := cut.faceInclusion
  alpha _ := rfl
  label _ := rfl
  outer := cut.faceInclusion_outer.symm
  face_boundary := by
    intro F hF
    obtain ⟨f, hf, rfl⟩ := exists_keptFace_of_ne_newFace Delta.toCombMap
      cut.outside cut.region F hF
    rw [cut.faceInclusion_kept]
    exact (replaceGRegionFaceBoundary_keptFace_map_val Delta.toCombMap
      cut.outside cut.region Delta.faceBoundary f hf).symm
  facePerm := by
    intro d hd
    have hnot : Delta.toCombMap.faceOf d.1 ∉ cut.outside := by
      intro hmem
      exact hd (faceOf_eq_newFace Delta.toCombMap cut.outside cut.region d hmem)
    exact (replaceGRegion_facePerm_val_of_notMem Delta.toCombMap cut.outside
      cut.region d hnot).symm

/-- A genuine inner G-region of the cut supplies its actual ambient boundary
with every dart in the same order. No ambient boundary certificate is input. -/
noncomputable def includeBoundary (cut : RegionCutWithGCells Delta)
    {faces : Finset cut.diagram.toCombMap.Face}
    (B : Embedded.FaceSetBoundary cut.diagram faces) :
    Embedded.FaceSetBoundary Delta (cut.inclusion.faceSet faces) :=
  cut.inclusion.boundary faces
    (fun h => (B.all_gCells cut.diagram.outerFace h).1 rfl) B

theorem includeBoundary_cycle (cut : RegionCutWithGCells Delta)
    {faces : Finset cut.diagram.toCombMap.Face}
    (B : Embedded.FaceSetBoundary cut.diagram faces) :
    (cut.includeBoundary B).cycle = B.cycle.map Subtype.val := rfl

/-- The actual shelling of an inner G-region also transports through the
constructed inclusion. -/
theorem includeShelling (cut : RegionCutWithGCells Delta)
    {faces : Finset cut.diagram.toCombMap.Face}
    (B : Embedded.FaceSetBoundary cut.diagram faces)
    {l : List cut.diagram.toCombMap.Face}
    (H : Embedded.FaceShelling cut.diagram faces l B.cycle) :
    Embedded.FaceShelling Delta (cut.inclusion.faceSet faces)
      (l.map cut.faceInclusion) (B.cycle.map Subtype.val) :=
  cut.inclusion.shelling faces
    (fun h => (B.all_gCells cut.diagram.outerFace h).1 rfl) H

end RegionCutWithGCells
end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.inclusion
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.includeBoundary
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.includeShelling
