import GroupApproximation.GGT.VanKampen.DiscEmbeddingAway
import GroupApproximation.GGT.VanKampen.SurgeryCellMap
import GroupApproximation.GGT.VanKampen.Estimating.CyclicArcMap

/-!
# Transport every field of an embedded contiguity through retained faces

The actual dart embedding retains the cyclic carriers and side words. The
ordered cell map retains the individual data used in O52. Together with the
already proved boundary and shelling transport, this gives a full contiguity
on the image region with the same side bounds and cyclic arc lengths.
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

include hcells in
theorem cellDarts_eq (i : Fin Delta.rCellCount) :
    cellDarts Xi (C.indexEquiv i) = (cellDarts Delta i).map E.darts := by
  change (Xi.faceBoundary (cell Xi (C.indexEquiv i)).face).darts = _
  rw [C.indexed_cell, C.face_eq]
  exact E.face_boundary _ (hcells _ (cell_mem Delta i))

include hf in
theorem outerDarts_eq : outerDarts Xi = (outerDarts Delta).map E.darts := by
  change invDarts Xi (Xi.faceBoundary Xi.outerFace).darts =
    (invDarts Delta (Delta.faceBoundary Delta.outerFace).darts).map E.darts
  rw [E.outer, E.face_boundary _ hf.symm]
  exact E.invDarts_map _

include hcells hf in
theorem targetDarts_eq (target : Option (Fin Delta.rCellCount)) :
    targetDarts Xi (target.map C.indexEquiv) = (targetDarts Delta target).map E.darts := by
  cases target with
  | none => exact E.outerDarts_eq hf
  | some i => exact E.cellDarts_eq C hcells i

theorem reverseDarts_mapTo {cycle : List Delta.toCombMap.Dart}
    (arc : CyclicArc cycle) {target : List Xi.toCombMap.Dart}
    (h : target = cycle.map E.darts) :
    (arc.mapTo E.darts h).reverseDarts = arc.reverseDarts.map E.darts := by
  change invDarts Xi (arc.mapTo E.darts h).darts = (invDarts Delta arc.darts).map E.darts
  rw [CyclicArc.mapTo_darts, E.invDarts_map]

theorem targetBoundaryDarts_map (target : Option (Fin Delta.rCellCount))
    (arc : CyclicArc (targetDarts Delta target)) :
    targetBoundaryDarts Xi (target.map C.indexEquiv)
      (arc.mapTo E.darts (E.targetDarts_eq C hcells hf target)) =
      (targetBoundaryDarts Delta target arc).map E.darts := by
  cases target with
  | none => exact arc.mapTo_darts E.darts _
  | some i => exact E.reverseDarts_mapTo arc _

/-- Full transport, including the exact ordered O52 certificate and the pasting witness. -/
def contiguity {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s)
    (H : Contiguity D eps Delta s) : Contiguity D eps Xi (E.faceSet s) where
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
  target_ne_source := by
    intro i hi heq
    obtain ⟨j, ht, hj⟩ := Option.map_eq_some_iff.mp hi
    exact H.target_ne_source j ht (C.indexEquiv.injective (heq.trans hj.symm))
  o52Certificate := by
    intro i hi
    obtain ⟨j, ht, hj⟩ := Option.map_eq_some_iff.mp hi
    subst i
    obtain ⟨pre, between, suf, hsplit, hsource, htarget, hsourceRot, htargetRot, hconnector⟩ :=
      H.o52Certificate j ht
    refine ⟨pre.map C.cell, between.map C.cell, suf.map C.cell, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [C.list_eq, hsplit, List.map_append, List.map_cons, List.map_append, List.map_cons,
        C.indexed_cell, C.indexed_cell]
    · rw [C.indexed_cell, C.reversed_eq]
      exact hsource
    · rw [C.indexed_cell, C.reversed_eq]
      exact htarget
    · rw [CyclicArc.mapTo_rotated, E.dartWord_map, C.indexed_cell, C.word_eq]
      exact hsourceRot
    · rw [CyclicArc.mapTo_rotated, E.dartWord_map, C.indexed_cell, C.word_eq]
      exact htargetRot
    · rw [CyclicArc.mapTo_darts, E.dartWord_map, E.dartWord_map,
        C.indexed_cell, C.indexed_cell, C.conjugator_eq, C.conjugator_eq, C.map_values]
      exact hconnector
  pasting := by
    obtain ⟨l, hl⟩ := H.pasting
    exact ⟨l.map E.faces, E.shelling s hs hl⟩

theorem contiguity_source_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s) (H : Contiguity D eps Delta s) :
    (E.contiguity C hcells hf hs H).sourceArc.length = H.sourceArc.length :=
  H.sourceArc.mapTo_length E.darts (E.cellDarts_eq C hcells H.source)

theorem contiguity_target_length {D : RelGenSet G Lambda} {eps : ℕ}
    {s : Finset Delta.toCombMap.Face} (hs : f ∉ s) (H : Contiguity D eps Delta s) :
    (E.contiguity C hcells hf hs H).targetArc.length = H.targetArc.length :=
  H.targetArc.mapTo_length E.darts (E.targetDarts_eq C hcells hf H.target)

end GroupApproximation.GGT.VanKampen.DiscEmbeddingAway

#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.contiguity
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.contiguity_source_length
#audit_axioms GroupApproximation.GGT.VanKampen.DiscEmbeddingAway.contiguity_target_length
