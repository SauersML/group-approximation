import GroupApproximation.GGT.VanKampen.SurgeryCutDiagram
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GroupTheory.NormalClosureReducedProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# Least area passes to cut pieces

Osin's induction on the number of `R`-cells applies clause (b) of Lemma 9.7 to
the subdiagram `Ξ` cut out by two contiguity regions.  The inductive hypothesis
is stated at least-area diagrams (`DiscDiagram.LeastArea`), so the piece must be
least area whenever the source is.  That is algebraic: the piece of a
`Surgery.MapCollapse.RegionCutData` keeps an infix of the source's ordered cells,
rebased by one element, and its boundary value is their rebased product.  A
shorter relator product for the piece's boundary would replace that infix in
the source's product and give a shorter filling of the source's boundary.

* `RelatorCell.value_isSignedConjugate`: every stored cell value is a signed
  conjugate of a relator.
* `DiscDiagram.isRelatorProduct_boundaryValue`: the boundary value of a disc
  diagram is a relator product with exactly `rCellCount` factors.
* `Surgery.MapCollapse.RegionCutData.diagram_leastArea`: least area passes to
  the cut piece.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- Every stored relator-cell value is a signed conjugate of a relator. -/
theorem RelatorCell.value_isSignedConjugate {G : Type u} [Group G] {Lambda : Type w}
    {M : CombMap.{v}} {outer : M.Face} {W : Set (List (RelLetter G Lambda))}
    (C : RelatorCell M outer W) :
    RelatorDefectBudget.IsSignedConjugate (RelLetter.listVal '' W) C.value := by
  refine ⟨C.conjugator, RelLetter.listVal C.word, ⟨C.word, C.word_mem, rfl⟩, ?_⟩
  rcases hrev : C.reversed with _ | _
  · left
    simp [RelatorCell.value, hrev]
  · right
    simp [RelatorCell.value, hrev]

/-- **The easy van Kampen count.**  The boundary value of a disc diagram is a
relator product with exactly as many factors as the diagram has relator cells. -/
theorem DiscDiagram.isRelatorProduct_boundaryValue {G : Type u} [Group G]
    {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) :
    RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W)
      Delta.rCellCount Delta.boundaryValue := by
  have h := RelatorDefectBudget.isRelatorProduct_prod_of_signedConjugates
    (Delta.relatorCells.map RelatorCell.value) (by
      intro x hx
      obtain ⟨C, _hC, rfl⟩ := List.mem_map.mp hx
      exact C.value_isSignedConjugate)
  rw [List.length_map, Delta.relatorValues_prod_eq_boundaryValue] at h
  exact h

/-- **Least area passes to the piece a cut encloses.** -/
theorem Surgery.MapCollapse.RegionCutData.diagram_leastArea {G : Type u} [Group G]
    {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (cut : Surgery.MapCollapse.RegionCutData Delta) (hlea : Delta.LeastArea) :
    cut.diagram.LeastArea := by
  intro m hm
  let c := cut.basepoint
  let infix := (cut.cells.map Subtype.val).map RelatorCell.value
  have hkept : cut.diagram.relatorCells.map RelatorCell.value =
      infix.map (fun x => c⁻¹ * x * c) := by
    show (cut.cells.map (Surgery.MapCollapse.keptRelatorCell Delta cut.outside
      cut.region cut.basepoint)).map RelatorCell.value = _
    simp only [infix, List.map_map]
    apply List.map_congr_left
    intro C _
    exact Surgery.MapCollapse.keptRelatorCell_value Delta cut.outside cut.region
      cut.basepoint C
  have hpiece : cut.diagram.boundaryValue = c⁻¹ * infix.prod * c := by
    rw [← cut.diagram.relatorValues_prod_eq_boundaryValue, hkept]
    have h := RelatorDefectBudget.prod_map_conj c⁻¹ infix
    simpa only [inv_inv] using h
  have hinfix : RelatorDefectBudget.IsRelatorProduct (RelLetter.listVal '' W) m
      infix.prod := by
    have h := hm.conj c
    rw [hpiece] at h
    have heq : c * (c⁻¹ * infix.prod * c) * c⁻¹ = infix.prod := by group
    rwa [heq] at h
  have hbefore := RelatorDefectBudget.isRelatorProduct_prod_of_signedConjugates
    (cut.before.map RelatorCell.value) (by
      intro x hx
      obtain ⟨C, _hC, rfl⟩ := List.mem_map.mp hx
      exact C.value_isSignedConjugate)
  have hafter := RelatorDefectBudget.isRelatorProduct_prod_of_signedConjugates
    (cut.after.map RelatorCell.value) (by
      intro x hx
      obtain ⟨C, _hC, rfl⟩ := List.mem_map.mp hx
      exact C.value_isSignedConjugate)
  have hsum := (hbefore.mul hinfix).mul hafter
  have hDelta : (cut.before.map RelatorCell.value).prod * infix.prod *
      (cut.after.map RelatorCell.value).prod = Delta.boundaryValue := by
    rw [← Delta.relatorValues_prod_eq_boundaryValue, cut.cells_infix]
    simp only [infix, List.map_append, List.prod_append]
  rw [hDelta] at hsum
  have hle := hlea hsum
  have hcount : Delta.rCellCount =
      cut.before.length + cut.cells.length + cut.after.length := by
    show Delta.relatorCells.length = _
    rw [cut.cells_infix]
    simp only [List.length_append, List.length_map]
  simp only [List.length_map] at hle
  rw [cut.diagram_rCellCount]
  omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.RelatorCell.value_isSignedConjugate
#audit_axioms GroupApproximation.GGT.VanKampen.DiscDiagram.isRelatorProduct_boundaryValue
#audit_axioms GroupApproximation.GGT.VanKampen.Surgery.MapCollapse.RegionCutData.diagram_leastArea
