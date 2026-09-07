import GroupApproximation.GGT.VanKampen.Estimating.Assembly
import GroupApproximation.GGT.VanKampen.SurgeryOrderedCells

/-!
# Estimating selection with transport of actual relator lists

These are the replacement consumers with the corrected interface from issue
#205. The historical full-type-equivalence consumers remain unchanged.
Constructing the local face-reducing replacements is still a geometric task.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- A corrected G-region replacement supplies every invariant in the face
drop branch, without a bijection of unlisted potential relator records. -/
theorem selection_drop_of_orderedGRegionReplacement
    {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))}
    {lambda c : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    (hred : Delta.Reduced) (hcells : 0 < Delta.rCellCount)
    (hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord)
    (replacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta)
    (hdrop : replacement.diagram.toCombMap.faceCount < Delta.toCombMap.faceCount) :
    ∃ Xi : DiscDiagram.{u, w, v} W,
      Nonempty (OEquivalentDiscDiagram Delta Xi) ∧
        Xi.toCombMap.faceCount < Delta.toCombMap.faceCount ∧
        Xi.Reduced ∧ 0 < Xi.rCellCount ∧
          IsLambdaCQuasiGeodesicWord D lambda c Xi.boundaryWord := by
  refine ⟨replacement.diagram, ⟨replacement.oEquivalent⟩, hdrop,
    replacement.reduced hred, ?_, replacement.oEquivalent.boundary_quasiGeodesic hboundary⟩
  rwa [replacement.cells.rCellCount_eq]

/-- Actual ordered-cell replacements feed the existing face-count induction. -/
theorem selectionFaceDropOracle_of_orderedGRegionReplacements
    {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    {W : Set (List (RelLetter G Lambda))}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hreplacement : ∀ (Delta : DiscDiagram.{u, w, v} W),
      Delta.Reduced → 0 < Delta.rCellCount →
      IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      (∃ scaffold : EstimatingScaffold D eps Delta,
        Nonempty (EstimatingGraphData D eps Delta scaffold)) ∨
      ∃ replacement : Surgery.OrderedGRegionReplacement.{u, w, v, v} Delta,
        replacement.diagram.toCombMap.faceCount < Delta.toCombMap.faceCount) :
    SelectionFaceDropOracle.{u, w, v} D eps rho mu lambda c hcondition := by
  intro Delta hred hcells hboundary
  rcases hreplacement Delta hred hcells hboundary with hterminal | hdrop
  · exact Or.inl hterminal
  · obtain ⟨replacement, hface⟩ := hdrop
    exact Or.inr (selection_drop_of_orderedGRegionReplacement hred hcells hboundary
      replacement hface)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.selection_drop_of_orderedGRegionReplacement
#audit_axioms GroupApproximation.GGT.VanKampen.selectionFaceDropOracle_of_orderedGRegionReplacements
