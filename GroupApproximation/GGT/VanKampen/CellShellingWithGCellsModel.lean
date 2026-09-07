import GroupApproximation.GGT.VanKampen.CellShellingWithGCells
import GroupApproximation.GGT.VanKampen.CellShellingSupportCounterexample

/-!
# The repaired shelling on the historical obstruction

Rotate the relator boundary to `[2, 1, 0]`, remove the bridge spur `[1, 0]`,
insert the actual G-cell digon `[3, 4]`, and cancel `[2, 3]`. The resulting
walk is the actual exterior `[4]`. The recorded trace still consists of the
single original relator, with its original conjugator.
-/

namespace GroupApproximation.GGT.VanKampen.CellShellingWithGCellsModel

open Embedded ExteriorArcCounterexample CellShellingSupportCounterexample

theorem relator_rotation :
    CellShellingWithGCells diagram innerFaces [b⁻¹]
      [orientedFaceDarts diagram (face 0) false] [2, 1, 0] := by
  classical
  have hface : face 0 ∈ innerFaces := by
    change face 0 ∈ ({face 0, face 1} : Finset M.Face)
    exact Finset.mem_insert_self _ _
  have hcd : orientedFaceDarts diagram (face 0) false =
      ([0, 2, 1] : List diagram.toCombMap.Dart) := boundary_face_darts 0
  apply CellShellingWithGCells.step (before := []) (arc := []) (after := [])
    (exposed := [2, 1, 0]) (face 0) hface false 1 (b⁻¹)
    (orientedFaceDarts diagram (face 0) false) rfl
  · rw [hcd]
    rfl
  · rw [hcd]
    change b⁻¹ = 1 * (b * 1)⁻¹
    simp
  · exact .empty

theorem gCell_boundary_moves :
    FaceSetWordHomotopy diagram faces [2, 1, 0] [4] := by
  have first : FaceSetWordHomotopy diagram faces [2, 1, 0] [2] :=
    .eraseAlphaPair 1 [2] []
  have middle : FaceSetWordHomotopy diagram faces [2] [2, 3, 4] := by
    have h := FaceSetWordHomotopy.eraseFace (Delta := diagram) (faces := faces)
      (face 1) (Finset.mem_singleton_self _) [2] []
    have hd : (diagram.faceBoundary (face 1)).darts = [3, 4] := boundary_face_darts 1
    rw [hd] at h
    exact h.symm
  have last : FaceSetWordHomotopy diagram faces [2, 3, 4] [4] :=
    .eraseAlphaPair 2 [] [4]
  exact first.trans (middle.trans last)

/-- The same outer walk excluded by the historical predicate has an explicit
shelling with exactly its original relator and conjugator. -/
theorem outer_shelling :
    CellShellingWithGCells diagram innerFaces [b⁻¹]
      [orientedFaceDarts diagram (face 0) false] (outerDarts diagram) := by
  classical
  rw [diagram_outerDarts]
  apply CellShellingWithGCells.gMove faces _ regionBoundary.all_gCells
    gCell_boundary_moves relator_rotation
  intro f hf
  have hf' : f = face 1 := Finset.mem_singleton.mp hf
  rw [hf']
  change face 1 ∈ ({face 0, face 1} : Finset M.Face)
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The repaired interface is inhabited on a reduced planar diagram where
the original interface is refuted, with the exact same recorded trace. -/
theorem strict_extension_on_reduced_diagram :
    diagram.Reduced ∧
      CellShellingWithGCells diagram innerFaces [b⁻¹]
        [orientedFaceDarts diagram (face 0) false] (outerDarts diagram) ∧
      ¬ CellShelling diagram innerFaces [b⁻¹]
        [orientedFaceDarts diagram (face 0) false] (outerDarts diagram) :=
  ⟨diagram_reduced, outer_shelling, not_outer_shelling⟩

end GroupApproximation.GGT.VanKampen.CellShellingWithGCellsModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellShellingWithGCellsModel.outer_shelling
#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellShellingWithGCellsModel.strict_extension_on_reduced_diagram
