import GroupApproximation.GGT.VanKampen.SurgeryOrderedCells
import GroupApproximation.GGT.VanKampen.NullWordDisc
import GroupApproximation.GGT.VanKampen.Estimating.UnboundEmptyDisc

/-!
# G-cell replacement need not preserve all potential relator records

Both explicit discs have the same boundary and empty relator lists, over a
nonempty family. The old one-edge map has no inner face, so its potential
relator-record type is empty. The new polygon has a G-face, which admits an
unlisted relator record. This refutes the full-type bijection requirement in
`Surgery.RCellEquiv` while exhibiting the corrected replacement (issue #205).
-/

namespace GroupApproximation.GGT.VanKampen.SurgeryRCellEquivCounterexample

open HullSC Estimating Surgery

abbrev Trivial := PUnit.{1}
def family : Set (List (RelLetter Trivial Trivial)) := {[RelLetter.comp PUnit.unit 1]}

/-- The one-edge diagram construction works over the nonempty family too. -/
noncomputable def oldDiagram : DiscDiagram.{0, 0, 0} family where
  toCombMap := emptyDiscMap
  planar := emptyDiscMap_planar
  label := fun _ => RelLetter.comp PUnit.unit 1
  label_alpha := by intro d; rfl
  outerFace := emptyDiscMap.faceOf false
  faceBoundary := emptyDiscFaceBoundary
  relatorCells := []
  relatorCell_faces_nodup := List.nodup_nil
  relatorCell_word := by intro C h; exact absurd h List.not_mem_nil
  inner_face := by intro f hf; exact (hf (emptyDiscMap_face_eq f)).elim
  boundary_product := Subsingleton.elim _ _

theorem old_word_nonempty : oldDiagram.faceWord oldDiagram.outerFace ≠ [] := by
  intro h
  exact (oldDiagram.faceBoundary oldDiagram.outerFace).nonempty (List.map_eq_nil_iff.1 h)

noncomputable def newDiagram : DiscDiagram.{0, 0, 0} family :=
  NullWordDisc.diagram family (oldDiagram.faceWord oldDiagram.outerFace)
    old_word_nonempty (Subsingleton.elim _ _)

theorem boundaryWord_eq : newDiagram.boundaryWord = oldDiagram.boundaryWord :=
  NullWordDisc.diagram_boundaryWord family _ _ _

noncomputable def newPotentialCell : RelatorCell newDiagram.toCombMap newDiagram.outerFace family where
  face := (NullWordDisc.shape (oldDiagram.faceWord oldDiagram.outerFace) old_word_nonempty).bigFace
  face_ne_outer := (NullWordDisc.shape _ old_word_nonempty).bigFace_ne_outerFace
  word := [RelLetter.comp PUnit.unit 1]
  word_mem := Set.mem_singleton _
  conjugator := 1
  reversed := false

theorem no_oldPotentialCell (C : RelatorCell oldDiagram.toCombMap oldDiagram.outerFace family) :
    False := C.face_ne_outer (emptyDiscMap_face_eq C.face)

theorem no_historical_transport : ¬ Nonempty (RCellEquiv oldDiagram newDiagram) := by
  rintro ⟨cells⟩
  exact no_oldPotentialCell (cells.cellEquiv.symm newPotentialCell)

noncomputable def correctedReplacement : OrderedGRegionReplacement oldDiagram :=
  ⟨newDiagram, boundaryWord_eq, OrderedRCellTransport.of_no_rCells rfl rfl⟩

/-- A closed counterexample: genuine reduced O-equivalent discs with empty
actual relator lists need not carry the historical full-type equivalence. -/
theorem ordered_replacement_without_full_equivalence :
    ∃ (W : Set (List (RelLetter Trivial Trivial))) (Delta Xi : DiscDiagram.{0, 0, 0} W),
      Delta.relatorCells = [] ∧ Xi.relatorCells = [] ∧ Delta.Reduced ∧ Xi.Reduced ∧
        Nonempty (OEquivalentDiscDiagram Delta Xi) ∧
          Nonempty (OrderedGRegionReplacement.{0, 0, 0, 0} Delta) ∧
            ¬ Nonempty (RCellEquiv Delta Xi) := by
  refine ⟨family, oldDiagram, newDiagram, rfl, rfl,
    DiscDiagram.reduced_of_no_rCells oldDiagram rfl,
    DiscDiagram.reduced_of_no_rCells newDiagram rfl,
    ⟨correctedReplacement.oEquivalent⟩, ⟨correctedReplacement⟩, no_historical_transport⟩

end GroupApproximation.GGT.VanKampen.SurgeryRCellEquivCounterexample

#audit_axioms GroupApproximation.GGT.VanKampen.SurgeryRCellEquivCounterexample.correctedReplacement
#audit_closed_axioms GroupApproximation.GGT.VanKampen.SurgeryRCellEquivCounterexample.no_historical_transport
#audit_closed_axioms GroupApproximation.GGT.VanKampen.SurgeryRCellEquivCounterexample.ordered_replacement_without_full_equivalence
