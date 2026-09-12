import GroupApproximation.GGT.VanKampen.SurgeryGCellCutInclusion

/-!
# The retained cell indices of an actual cut

The retained block begins after the source prefix. This explicit index
injection identifies each cut cell with its original face and word, while
retaining the common change of basepoint in its value. Its face boundaries
then agree under the actual dart inclusion, with their original start.
-/

namespace GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells

open Embedded
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

noncomputable def retainedCell (cut : RegionCutWithGCells Delta) (i : Fin cut.diagram.rCellCount) :
    {C : RelatorCell Delta.toCombMap Delta.outerFace W // C.face ∉ cut.outside} :=
  cut.cells.get (Fin.cast cut.diagram_rCellCount i)

/-- The actual source position of a retained cell. -/
def cellInclusion (cut : RegionCutWithGCells Delta) :
    Fin cut.diagram.rCellCount ↪ Fin Delta.rCellCount where
  toFun i := ⟨cut.before.length + i.val, by
    have hi : i.val < cut.cells.length := by simpa only [cut.diagram_rCellCount] using i.isLt
    have hlen := congrArg List.length cut.cells_infix
    simp only [List.length_append, List.length_map] at hlen
    change cut.before.length + i.val < Delta.relatorCells.length
    omega⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (congrArg Fin.val hij)

theorem cellInclusion_val (cut : RegionCutWithGCells Delta) (i : Fin cut.diagram.rCellCount) :
    (cut.cellInclusion i).val = cut.before.length + i.val := rfl

/-- The map retains the source order, as required by the cut's cell block. -/
theorem cellInclusion_lt_iff (cut : RegionCutWithGCells Delta)
    (i j : Fin cut.diagram.rCellCount) : cut.cellInclusion i < cut.cellInclusion j ↔ i < j := by
  change cut.before.length + i.val < cut.before.length + j.val ↔ i.val < j.val
  omega

theorem indexed_cut_cell (cut : RegionCutWithGCells Delta) (i : Fin cut.diagram.rCellCount) :
    cell cut.diagram i =
      keptRelatorCell Delta cut.outside cut.region cut.basepoint (cut.retainedCell i) := by
  change (cut.cells.map (keptRelatorCell Delta cut.outside cut.region cut.basepoint)).get i = _
  simp only [List.get_eq_getElem, List.getElem_map]
  rfl

theorem indexed_source_cell (cut : RegionCutWithGCells Delta) (i : Fin cut.diagram.rCellCount) :
    cell Delta (cut.cellInclusion i) = (cut.retainedCell i).1 := by
  have hi : i.val < cut.cells.length := by simpa only [cut.diagram_rCellCount] using i.isLt
  have hlook : Delta.relatorCells[(cut.cellInclusion i).val]? =
      some (cut.retainedCell i).1 := by
    change Delta.relatorCells[cut.before.length + i.val]? = _
    rw [cut.cells_infix, List.append_assoc,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa only [List.length_map] using hi),
      List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl
  simp only [List.getElem?_eq_getElem (cut.cellInclusion i).isLt,
    Option.some.injEq] at hlook
  exact hlook

theorem faceInclusion_cell (cut : RegionCutWithGCells Delta) (i : Fin cut.diagram.rCellCount) :
    cut.faceInclusion (cell cut.diagram i).face = (cell Delta (cut.cellInclusion i)).face := by
  rw [cut.indexed_cut_cell, cut.indexed_source_cell]
  exact cut.faceInclusion_kept _ _

theorem cellWord_eq (cut : RegionCutWithGCells Delta) (i : Fin cut.diagram.rCellCount) :
    (cell cut.diagram i).word = (cell Delta (cut.cellInclusion i)).word := by
  rw [cut.indexed_cut_cell, cut.indexed_source_cell]
  rfl

theorem cellValue_eq (cut : RegionCutWithGCells Delta) (i : Fin cut.diagram.rCellCount) :
    (cell cut.diagram i).value =
      cut.basepoint⁻¹ * (cell Delta (cut.cellInclusion i)).value * cut.basepoint := by
  rw [cut.indexed_cut_cell, cut.indexed_source_cell]
  exact keptRelatorCell_value Delta cut.outside cut.region cut.basepoint _

/-- The entire cyclic relator carrier, including its chosen start, returns
to its source carrier under the actual inclusion. -/
theorem cellDarts_eq (cut : RegionCutWithGCells Delta) (i : Fin cut.diagram.rCellCount) :
    cellDarts Delta (cut.cellInclusion i) = (cellDarts cut.diagram i).map Subtype.val := by
  change (Delta.faceBoundary (cell Delta (cut.cellInclusion i)).face).darts = _
  rw [← cut.faceInclusion_cell]
  exact cut.inclusion.face_boundary _ (cell cut.diagram i).face_ne_outer

end GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells

#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.indexed_source_cell
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.cellInclusion_lt_iff
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.cellValue_eq
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutWithGCells.cellDarts_eq
