import GroupApproximation.GGT.VanKampen.CellShellingWithGCells
import GroupApproximation.GGT.VanKampen.SurgeryCutCells
import GroupApproximation.GGT.VanKampen.Estimating.Embedded
import GroupApproximation.Meta.AxiomGuard

/-!
# Disc diagrams that carry a shelling

A `DiscDiagram` ties its stored cell conjugators to its planar structure only
through the product formula `boundary_product`.  Osin's surgeries in the proof
of Lemma 9.7 (cutting a subdiagram out, removing a cancelling pair of cells and
refilling the hole) need the product formula of the NEW diagram, and on main a
surgery gets it only from carried data: `Surgery.MapCollapse.RegionCutData`
carries a `CellShelling` of the enclosed faces along the cut walk
(`SurgeryCutProduct.keptCells_value_prod`).  Proving that every planar disc map
has such a shelling would need an ear theorem (`FaceSetEarStatement` is only
available from ear data).

`ShelledDiscDiagram` is the carried-data alternative, as a NEW structure so that
no existing constructor of `DiscDiagram` moves: a disc diagram together with a
recorded shelling of its faces along the exterior walk `outerDarts`, whose
recorded relator steps are exactly the stored cells, in the stored order, with
the stored conjugators and orientations.  Realizations and surgery outputs used
in the induction produce shelled diagrams, and the product formula of a surgery
output is read off the transported shelling.

* `ShelledDiscDiagram.cellValue_eq_step`: a recorded step contributes exactly the
  stored cell value.
* `ShelledDiscDiagram.boundaryValue_eq_shelling`: the shelling's own van Kampen
  product formula (`Embedded.listVal_dartWord_of_cellShellingWithGCells`).
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- **A disc diagram with a recorded shelling** of its faces along the exterior
walk.  The recorded relator steps are the stored cells, in order, each with its
stored conjugator and orientation; null faces may be crossed by recorded
face-set word homotopies. -/
structure ShelledDiscDiagram {G : Type u} [Group G] {Lambda : Type w}
    (W : Set (List (RelLetter G Lambda))) where
  /-- The underlying disc diagram. -/
  toDiscDiagram : DiscDiagram.{u, w, v} W
  /-- The shelling, along the exterior walk. -/
  shelling : Embedded.CellShellingWithGCells toDiscDiagram Finset.univ
    (toDiscDiagram.relatorCells.map RelatorCell.conjugator)
    (toDiscDiagram.relatorCells.map fun C =>
      Embedded.orientedFaceDarts toDiscDiagram C.face C.reversed)
    (Embedded.outerDarts toDiscDiagram)

namespace ShelledDiscDiagram

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

/-- A recorded step contributes exactly the stored cell value. -/
theorem cellValue_eq_step (Delta : ShelledDiscDiagram.{u, w, v} W)
    (C : RelatorCell Delta.toDiscDiagram.toCombMap Delta.toDiscDiagram.outerFace W)
    (hC : C ∈ Delta.toDiscDiagram.relatorCells) :
    C.value = C.conjugator *
      RelLetter.listVal (Embedded.dartWord Delta.toDiscDiagram
        (Embedded.orientedFaceDarts Delta.toDiscDiagram C.face C.reversed)) *
      C.conjugator⁻¹ := by
  rw [RelatorCell.value_eq_conj, Embedded.listVal_orientedFaceDarts,
    Delta.toDiscDiagram.relatorCell_word C hC, DiscDiagram.faceWord]

/-- **The shelling's product formula**: the boundary value is the ordered product
of the recorded conjugated steps. -/
theorem boundaryValue_eq_shelling (Delta : ShelledDiscDiagram.{u, w, v} W) :
    Delta.toDiscDiagram.boundaryValue =
      (List.zipWith
        (fun g cd =>
          g * RelLetter.listVal (Embedded.dartWord Delta.toDiscDiagram cd) * g⁻¹)
        (Delta.toDiscDiagram.relatorCells.map RelatorCell.conjugator)
        (Delta.toDiscDiagram.relatorCells.map fun C =>
          Embedded.orientedFaceDarts Delta.toDiscDiagram C.face C.reversed)).prod := by
  have h := Embedded.listVal_dartWord_of_cellShellingWithGCells Delta.shelling
  rw [Embedded.dartWord_outerDarts] at h
  exact h

end ShelledDiscDiagram

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.ShelledDiscDiagram.cellValue_eq_step
#audit_axioms GroupApproximation.GGT.VanKampen.ShelledDiscDiagram.boundaryValue_eq_shelling
