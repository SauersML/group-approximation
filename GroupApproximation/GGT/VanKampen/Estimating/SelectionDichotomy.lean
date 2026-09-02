import GroupApproximation.GGT.VanKampen.Estimating.SelectionSelfIncidence

/-!
# Lemma 65(a) reduced to one geometric dichotomy

Everything finite in `EstimatingSelectionConstructionStatement` is already
proved: Definition `M` selection, the face-count induction
(`selection_output_of_faceDropOracle`), the composition of `O`-equivalences,
the retyping of a `Surgery.GRegionReplacement` into an
`OEquivalentDiscDiagram`, and the transport of reducedness, relator count and
boundary quasi-geodesicity through it.

What is left is one dichotomy per reduced diagram: either the diagram already
carries the estimating-graph certificates, or it admits a region replacement
with strictly fewer ambient faces.  `Lemma65aDichotomyStatement` names exactly
that, at the construction statement's own quantifiers, and
`estimatingSelectionConstruction_of_lemma65aDichotomy` closes the construction
from it.

Its terminal branch asks for only **two** certificates rather than three:
loop separation is free, since `Embedded.Contiguity.target_ne_source` rules out
the self-contiguous candidates that `SelfIncidenceSeparated` constrains.  See
`Estimating/SelectionSelfIncidence.lean`.

The drop branch is where the missing map-level surgery sits.
`SurgeryMap.replaceGRegion` builds the collapsed `CombMap` and proves it planar
and connected, but nothing describes its *faces*, so the retyped `DiscDiagram`,
and hence `Surgery.GRegionReplacement`, cannot yet be constructed.  That is the
single cross-lane gap behind this statement.
-/

set_option linter.unusedVariables false

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v

/-! ## The planar edge bound, reduced to realizing Osin's incidence graph -/

/-- **Osin's `Phi_M` drawn in the diagram.**  For every sub-selection of cells
and interior edges that covers, the incidence graph is realized by a connected
planar combinatorial map with face degrees at least three, on the same number
of vertices and edges.  This is the only remaining input to the hereditary
planar edge bound; the Euler estimate itself is already proved as
`CombMap.edgeCount_le_three_mul_vertex_sub_one`. -/
def InteriorIncidencePlanarRealization : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Embedded.Candidate D eps Delta))
    (vertices : Finset (Fin Delta.rCellCount))
    (edges : Finset (Embedded.InteriorEdge selected)),
    EdgesCovered (Embedded.InteriorEdge.Incident (selected := selected))
        vertices edges →
      vertices.Nonempty →
      ∃ M : CombMap.{v}, M.IsPlanar ∧
        (∀ face : M.Face, 3 ≤ M.faceDegree face) ∧
        M.vertexCount = vertices.card ∧ M.edgeCount = edges.card

/-- **The hereditary planar edge bound from the realization.**  Osin's Lemma
`Eul` inequality is `CombMap.edgeCount_le_three_mul_vertex_sub_one`, already
proved; realizing the incidence graph as a planar map is the whole remaining
content. -/
theorem hasHereditaryPlanarEdgeBound_of_realization
    (hrealization : InteriorIncidencePlanarRealization.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Embedded.Candidate D eps Delta)) :
    HasHereditaryPlanarEdgeBound
      (Embedded.InteriorEdge.Incident (selected := selected)) := by
  intro vertices edges hcovered hnonempty
  obtain ⟨M, hplanar, hface, hvertex, hedge⟩ :=
    hrealization selected vertices edges hcovered hnonempty
  rw [← hedge, ← hvertex]
  exact M.edgeCount_le_three_mul_vertex_sub_one hplanar hface

/-- **The one geometric dichotomy left in Lemma 65(a).**  For every reduced,
positive-cell, quasi-geodesic diagram: either some scaffold carries the
hereditary planar edge bound and the admissible exterior merge, or the diagram
admits a region replacement with a strictly smaller ambient face count. -/
def Lemma65aDichotomyStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    (∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
      ∀ lambda c mu : ℝ,
        0 < lambda → lambda ≤ 1 → 0 ≤ c →
        0 < mu → mu ≤ 1 / 16 →
          ∃ eps rho : ℕ, 0 < rho ∧
            1 ≤ 2 * mu * Real.sqrt (rho : ℝ) ∧
            ∀ (W : Set (List (GGT.RelLetter G Lambda))),
              OsinCCondition D W eps mu lambda c rho →
                ∀ Delta : DiscDiagram.{u, w, v} W,
                  Delta.Reduced → 0 < Delta.rCellCount →
                  IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
                  (∃ scaffold : EstimatingScaffold D eps Delta,
                    HasHereditaryPlanarEdgeBound
                        (Embedded.InteriorEdge.Incident
                          (selected := scaffold.selected.family)) ∧
                      Embedded.ExteriorMergeAvailable
                        scaffold.selected.family) ∨
                  ∃ replacement :
                      Surgery.GRegionReplacement.{u, w, v, v} Delta,
                    replacement.diagram.toCombMap.faceCount <
                      Delta.toCombMap.faceCount

/-- **The selection construction from the dichotomy.**  The face-count
induction, the `O`-equivalence composition and the replacement retyping are all
landed, and loop separation is free, so the dichotomy is the whole remaining
input. -/
theorem estimatingSelectionConstruction_of_lemma65aDichotomy
    (hdichotomy : Lemma65aDichotomyStatement.{u, w, v}) :
    EstimatingSelectionConstructionStatement.{u, w, v} := by
  apply estimatingSelectionConstruction_of_faceDropOracles
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, hrho, hthreshold, hdich⟩ :=
    hdichotomy D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, hthreshold, ?_⟩
  intro W hcondition
  apply selectionFaceDropOracle_of_gRegionReplacements
  intro Delta hred hcells hboundary
  rcases hdich W hcondition Delta hred hcells hboundary with
    ⟨scaffold, hplanar, hmerge⟩ | hdrop
  · exact Or.inl ⟨scaffold,
      estimatingGraphData_of_planar_and_merge scaffold hplanar hmerge⟩
  · exact Or.inr hdrop

end VanKampen
end GGT
end GroupApproximation
