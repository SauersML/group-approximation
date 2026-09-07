import GroupApproximation.GGT.VanKampen.GCellCutSourceModel
import GroupApproximation.GGT.VanKampen.SurgeryGCellCutSections
import GroupApproximation.GGT.VanKampen.SurgeryGCellCutContiguity
import GroupApproximation.GGT.VanKampen.SurgeryReclosedPlanarity

/-!
# An actual cell-dropping cut that needs the repaired shelling

The outside consists of the original exterior and a relator monogon. Its
genuine boundary is `[5]`; reclosing removes the monogon's edge pair. The cut
retains the bridged relator and the adjacent G-cell digon, with exterior `[4]`.
The source and cut are reduced, and the cell count drops from two to one.
The corrected shelling constructs the cut and its Lemma 6.5 boundary data.
The historical shelling is impossible on this very cut boundary.

This model validates the auxiliary surgery interface. It does not assert the
small-cancellation hypotheses or produce every cut used in Osin's induction.
-/

namespace GroupApproximation.GGT.VanKampen.GCellCutModel

open Embedded Surgery.MapCollapse GCellCutSourceModel
open ExteriorArcCounterexample (G a b D)
open scoped Classical

noncomputable def outside : Finset M.Face := {face 2, face 3}
noncomputable def enclosed : Finset M.Face := {face 0, face 1}
def gFaces : Finset M.Face := {face 1}

theorem internal_iff (d : Fin 8) :
    InternalDart M outside d ↔ d = 6 ∨ d = 7 := by
  simp only [InternalDart, outside, Finset.mem_insert, Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

theorem boundary_iff (d : Fin 8) :
    Surgery.MapCollapse.IsBoundaryDart M outside d ↔ d = 5 := by
  simp only [Surgery.MapCollapse.IsBoundaryDart, outside, Finset.mem_insert,
    Finset.mem_singleton, faceOf_eq_face]
  fin_cases d <;> decide

def actualBoundary : BoundaryCycle M outside where
  cycle := [5]
  cycle_nonempty := by decide
  cycle_nodup := by decide
  cycle_mem_iff := by intro d; rw [List.mem_singleton]; exact (boundary_iff d).symm

theorem actualBoundary_follows : actualBoundary.FollowsBoundary := by
  apply BoundaryCycle.followsBoundary_of_chain
  · exact List.isChain_singleton _
  · have h76 : Relation.ReflTransGen
        (fun x y : M.Dart => InternalDart M outside x ∧ M.sigma x = y) 7 6 :=
      .single ⟨(internal_iff 7).mpr (Or.inr rfl), rfl⟩
    have h65 : Relation.ReflTransGen
        (fun x y : M.Dart => InternalDart M outside x ∧ M.sigma x = y) 6 5 :=
      .single ⟨(internal_iff 6).mpr (Or.inl rfl), rfl⟩
    exact h76.trans h65

noncomputable def region : IsDiscRegion M outside :=
  actualBoundary.toDiscRegion_of_followsBoundary M outside actualBoundary_follows planar

theorem null_gFaces : ∀ f ∈ gFaces, f ≠ diagram.outerFace ∧
    RelLetter.listVal (diagram.faceWord f) = 1 := by
  intro f hf
  have hf' : f = face 1 := Finset.mem_singleton.mp hf
  subst f
  refine ⟨(face_eq_iff 1 3).not.mpr (by decide), ?_⟩
  change RelLetter.listVal ((boundary (face 1)).darts.map label) = 1
  rw [boundary_face_darts]
  change a⁻¹ * (a * 1) = 1
  simp

theorem relator_rotation : CellShellingWithGCells diagram enclosed [b⁻¹]
    [orientedFaceDarts diagram (face 0) false] [2, 1, 0] := by
  have hcd : orientedFaceDarts diagram (face 0) false =
      ([0, 2, 1] : List diagram.toCombMap.Dart) := boundary_face_darts 0
  apply CellShellingWithGCells.step (before := []) (arc := []) (after := [])
    (exposed := [2, 1, 0]) (face 0) (Finset.mem_insert_self _ _) false 1 (b⁻¹)
    (orientedFaceDarts diagram (face 0) false) rfl
  · rw [hcd]; rfl
  · rw [hcd]
    change b⁻¹ = 1 * (b * 1)⁻¹
    simp
  · exact .empty

theorem gCell_boundary_moves : FaceSetWordHomotopy diagram gFaces [2, 1, 0] [4] := by
  have first : FaceSetWordHomotopy diagram gFaces [2, 1, 0] [2] :=
    .eraseAlphaPair 1 [2] []
  have middle : FaceSetWordHomotopy diagram gFaces [2] [2, 3, 4] := by
    have h := FaceSetWordHomotopy.eraseFace (Delta := diagram) (faces := gFaces)
      (face 1) (Finset.mem_singleton_self _) [2] []
    have hd : (diagram.faceBoundary (face 1)).darts = [3, 4] := boundary_face_darts 1
    rw [hd] at h
    exact h.symm
  have last : FaceSetWordHomotopy diagram gFaces [2, 3, 4] [4] :=
    .eraseAlphaPair 2 [] [4]
  exact first.trans (middle.trans last)

theorem enclosing_shelling : CellShellingWithGCells diagram enclosed [b⁻¹]
    [orientedFaceDarts diagram (face 0) false] [4] := by
  apply CellShellingWithGCells.gMove gFaces _ null_gFaces gCell_boundary_moves relator_rotation
  intro f hf
  have hf' : f = face 1 := Finset.mem_singleton.mp hf
  rw [hf']
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

def kept : {C : RelatorCell diagram.toCombMap diagram.outerFace W // C.face ∉ outside} :=
  ⟨relatorCell, by
    change face 0 ∉ outside
    simp only [outside, Finset.mem_insert, Finset.mem_singleton, face_eq_iff]
    decide⟩

/-- The actual cut uses a proved reclosure and the explicit G-cell shelling.
Its ordered retained block is the last of the two source cells. -/
noncomputable def cut : RegionCutWithGCells diagram where
  outside := outside
  outer_mem := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  region := region
  enclosed := enclosed
  basepoint := 1
  cells := [kept]
  before := [removedCell]
  after := []
  cells_infix := rfl
  cut_faces := by
    intro C hC
    have h : C = removedCell := List.mem_singleton.mp hC
    subst C
    exact Finset.mem_insert_self _ _
  dropped := List.cons_ne_nil _ _
  arcs := [[5]]
  arcs_flatten := rfl
  shelling := by
    change CellShellingWithGCells diagram enclosed [1⁻¹ * b⁻¹]
      [orientedFaceDarts diagram (face 0) false] [4]
    simpa only [inv_one, one_mul] using enclosing_shelling

/-- The historical shelling fails for this actual cell-dropping cut. -/
theorem no_historical_cut_shelling :
    ¬ CellShelling diagram enclosed [b⁻¹]
      [orientedFaceDarts diagram (face 0) false]
      (invDarts diagram region.toBoundaryCycle.cycle) := by
  intro h
  obtain ⟨cd, hcd, hd⟩ := h.mem_recorded_face 4 (by change (4 : Fin 8) ∈ [4]; simp)
  have heq := List.mem_singleton.mp hcd
  subst cd
  change (4 : Fin 8) ∈ (boundary (face 0)).darts at hd
  rw [boundary_face_darts] at hd
  exact (by decide : (4 : Fin 8) ∉ faceDarts 0) hd

theorem cut_cell_count : cut.diagram.rCellCount = 1 :=
  cut.diagram_rCellCount

theorem cut_outer_walk : (outerDarts cut.diagram).map Subtype.val = [(4 : Fin 8)] :=
  cut.diagram_outerDarts_map_val

noncomputable def retainedIndex : Fin cut.diagram.rCellCount :=
  ⟨0, by rw [cut_cell_count]; decide⟩

/-- The retained cell was second in the source, so its inclusion is not
the identity on positions. -/
theorem retainedIndex_source : cut.cellInclusion retainedIndex =
    (⟨1, by change 1 < 2; decide⟩ : Fin diagram.rCellCount) := by
  apply Fin.ext
  rfl

theorem actual_retained_carrier :
    (cellDarts cut.diagram retainedIndex).map cut.inclusion.darts =
      [(0 : Fin 8), 2, 1] := by
  change (cellDarts cut.diagram retainedIndex).map Subtype.val = _
  rw [← cut.cellDarts_eq, retainedIndex_source]
  exact boundary_face_darts 0

noncomputable def cutExteriorArc : CyclicArc (targetDarts cut.diagram none) where
  start := ⟨0, Nat.zero_lt_succ _⟩
  length := (targetDarts cut.diagram none).length
  length_le := le_rfl

/-- The cut's exterior is the second dart of the original exterior. -/
def ambientExteriorArc : CyclicArc (targetDarts diagram none) where
  start := ⟨1, by decide⟩
  length := 1
  length_le := by decide

/-- The exact oriented arc premise of ambient transport is inhabited on
the actual reduced two-to-one cut. -/
theorem actual_exterior_arc_match :
    targetBoundaryDarts diagram none ambientExteriorArc =
      (targetBoundaryDarts cut.diagram none cutExteriorArc).map cut.inclusion.darts := by
  change [(4 : Fin 8)] = cutExteriorArc.darts.map cut.inclusion.darts
  simp only [CyclicArc.darts, CyclicArc.rotated, cutExteriorArc,
    List.drop_zero, List.take_zero, List.append_nil, List.take_length]
  exact cut_outer_walk.symm

theorem section_quasi : IsLambdaCQuasiGeodesicWord D 1 1 (dartWord diagram [4]) := by
  refine ⟨?_, ?_⟩
  · change GroupApproximation.HullSC.RelWord.IsAdmissible D [RelLetter.base a]
    intro x hx
    have hx' : x = RelLetter.base a := List.mem_singleton.mp hx
    subst x
    exact Set.mem_univ _
  · intro i j hij hj
    have hj' : j ≤ 1 := hj
    have hlen : ((j - i : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show j - i ≤ 1 by omega)
    apply le_trans (show (1 : ℝ) * ((j - i : ℕ) : ℝ) - 1 ≤ 0 by linarith)
    exact Nat.cast_nonneg _

/-- The repaired consumer constructs all the current Lemma 6.5 cut fields
on an actual reduced two-to-one cut with its original boundary word. -/
theorem exists_lemma65_cut : Nonempty (Lemma65CutData D 1 1 diagram) := by
  apply cut.exists_lemma65CutData_of_partition D 1 1 diagram_reduced
    (by rw [cut_cell_count]; decide) [[4]] (by decide) (by decide) rfl
  intro part hp
  have hp' : part = [4] := List.mem_singleton.mp hp
  subst part
  exact section_quasi

theorem actual_reduced_cut :
    diagram.Reduced ∧ diagram.rCellCount = 2 ∧ cut.diagram.Reduced ∧
      cut.diagram.rCellCount = 1 ∧
      (outerDarts cut.diagram).map Subtype.val = [(4 : Fin 8)] :=
  ⟨diagram_reduced, rfl, cut.diagram_reduced diagram_reduced, cut_cell_count, cut_outer_walk⟩

end GroupApproximation.GGT.VanKampen.GCellCutModel

#audit_closed_axioms GroupApproximation.GGT.VanKampen.GCellCutModel.no_historical_cut_shelling
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GCellCutModel.exists_lemma65_cut
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GCellCutModel.actual_reduced_cut
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GCellCutModel.retainedIndex_source
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GCellCutModel.actual_retained_carrier
#audit_closed_axioms GroupApproximation.GGT.VanKampen.GCellCutModel.actual_exterior_arc_match
