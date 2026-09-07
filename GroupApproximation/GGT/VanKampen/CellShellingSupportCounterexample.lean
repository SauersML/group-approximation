import GroupApproximation.GGT.VanKampen.FaceShellingValue
import GroupApproximation.GGT.VanKampen.ExteriorArcCounterexample
import GroupApproximation.GGT.VanKampen.Estimating.PieceCore

/-!
# The historical recorded shelling cannot traverse unrecorded G-cells

Every dart on its final walk must occur in a recorded face word. The cut
record fixes those words to the retained relator faces only. A genuine planar
diagram with one relator and a G-cell digon already has an exterior dart
absent from that trace, so its boundary admits no such recorded shelling.
The old predicate is retained with this explicit obstruction.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {Delta : DiscDiagram.{u, w, v} W}

/-- Historical shelling can only expose darts occurring in recorded faces. -/
theorem CellShelling.mem_recorded_face {faces : Finset Delta.toCombMap.Face}
    {gs : List G} {cds : List (List Delta.toCombMap.Dart)}
    {walk : List Delta.toCombMap.Dart} (h : CellShelling Delta faces gs cds walk) :
    ∀ d ∈ walk, ∃ cd ∈ cds, d ∈ cd := by
  induction h with
  | empty => intro d hd; cases hd
  | @step gs cds before arc after exposed face hface rev k g cd hcd hrot hg rest ih =>
      intro d hd
      have hrest : ∀ x ∈ before ++ arc ++ after, ∃ c ∈ cd :: cds, x ∈ c := by
        intro x hx
        obtain ⟨c, hc, hxc⟩ := ih x hx
        exact ⟨c, List.mem_cons.mpr (Or.inr hc), hxc⟩
      simp only [List.mem_append] at hd
      rcases hd with (hd | hd) | hd
      · exact hrest d (by simp only [List.mem_append]; exact Or.inl (Or.inl hd))
      · refine ⟨cd, List.mem_cons_self, ?_⟩
        have hmem : d ∈ cd.rotate k := by
          rw [hrot]
          exact List.mem_append.mpr (Or.inl hd)
        simpa using hmem
      · exact hrest d (by simp only [List.mem_append]; exact Or.inr hd)

end GroupApproximation.GGT.VanKampen.Embedded

namespace GroupApproximation.GGT.VanKampen.CellShellingSupportCounterexample

open Embedded ExteriorArcCounterexample

noncomputable def innerFaces : Finset diagram.toCombMap.Face := by
  classical
  exact {face 0, face 1}

theorem diagram_reduced : diagram.Reduced :=
  reduced_of_rCellCount_le_one diagram (by decide)

/-- The entire one-relator planar disc is already outside the historical
shelling interface, independently of the proposed conjugators. -/
theorem no_recorded_relator_shelling (faces : Finset diagram.toCombMap.Face) (gs : List G) :
    ¬ CellShelling diagram faces gs
      (diagram.relatorCells.map (fun C => orientedFaceDarts diagram C.face C.reversed))
      (outerDarts diagram) := by
  intro h
  obtain ⟨cd, hcd, hd⟩ := h.mem_recorded_face 4 (by rw [diagram_outerDarts]; simp)
  change cd ∈ [orientedFaceDarts diagram (face 0) false] at hcd
  have heq := List.mem_singleton.mp hcd
  subst cd
  change (4 : Fin 6) ∈ (boundary (face 0)).darts at hd
  rw [boundary_face_darts] at hd
  exact (by decide : (4 : Fin 6) ∉ faceDarts 0) hd

/-- A concrete closed obstruction with the source diagram's recorded
conjugator and its actual exterior walk. -/
theorem not_outer_shelling :
    ¬ CellShelling diagram innerFaces [b⁻¹]
      [orientedFaceDarts diagram (face 0) false] (outerDarts diagram) :=
  no_recorded_relator_shelling _ _

end GroupApproximation.GGT.VanKampen.CellShellingSupportCounterexample

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.CellShelling.mem_recorded_face
#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellShellingSupportCounterexample.diagram_reduced
#audit_closed_axioms GroupApproximation.GGT.VanKampen.CellShellingSupportCounterexample.not_outer_shelling
