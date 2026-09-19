import GroupApproximation.GGT.VanKampen.Estimating.EndpointClosedDeletion
import GroupApproximation.GGT.VanKampen.Estimating.SelectionSelfIncidence

/-!
# Estimating systems from endpoint-closed graph certificates

The historical `EstimatingGraphData` and `EstimatingData` require an Euler
bound even on states missing an edge's second endpoint, and hence forbid all
interior edges (#204). They remain unchanged for their regression refutations.
This module carries the corrected invariant through deletion, edge charging,
and the original `EmbeddedEstimatingSystem` and Greendlinger conclusions.

The geometric producer must choose the graph and Lemma 62 budget at the same
parameters. `EstimatingJointConstructionStatement` expresses this requirement
without the refuted universal unbound input (#198). The reductions below do
not assert that this geometric producer has been constructed.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.HullSC

universe u w v

/-- Corrected Lemma 65(a) data. The Euler inequality is required only for
subgraphs retaining all endpoints. Loop separation follows from the existing
contiguity definition, so it need not be an additional input. -/
structure EndpointClosedEstimatingGraphData
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta) where
  planarEdgeBound : HasEndpointClosedPlanarEdgeBound
    (Embedded.InteriorEdge.Incident (selected := scaffold.selected.family))
  exteriorMergeAvailable :
    Embedded.ExteriorMergeAvailable scaffold.selected.family

namespace EndpointClosedEstimatingGraphData

variable {G : Type u} [Group G] {Lambda : Type w}
  {D : GGT.RelGenSet G Lambda}
  {W : Set (List (GGT.RelLetter G Lambda))}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {scaffold : EstimatingScaffold D eps Delta}

/-- The actual interior incidence graph has a five-deletion order. The full
vertex set is endpoint-closed, and every subsequent deletion preserves that
invariant. -/
theorem fiveDeletionOrder
    (graph : EndpointClosedEstimatingGraphData D eps Delta scaffold) :
    Nonempty (FiveDeletionOrder
      (Embedded.InteriorEdge.Incident (selected := scaffold.selected.family))
      Finset.univ Finset.univ) := by
  apply exists_fiveDeletionOrder_of_endpointClosedPlanarEdgeBound
    Embedded.InteriorEdge.Incident
    Embedded.InteriorEdge.hasAtMostTwoEndpoints graph.planarEdgeBound
    Finset.univ Finset.univ Embedded.InteriorEdge.edgesCovered_univ
  exact edgesEndpointClosed_univ _ _

/-- The corrected graph produces the same five-owner orientation used in
Osin's Lemma Eul. -/
theorem fiveOwnerOrientation
    (graph : EndpointClosedEstimatingGraphData D eps Delta scaffold)
    (hcells : 0 < Delta.rCellCount) :
    Nonempty (FiveOwnerOrientation
      (Embedded.InteriorEdge.Incident (selected := scaffold.selected.family))
      Finset.univ Finset.univ) := by
  letI : Nonempty (Fin Delta.rCellCount) := Fin.pos_iff_nonempty.mp hcells
  obtain ⟨order⟩ := graph.fiveDeletionOrder
  exact FiveDeletionOrder.toOwnerOrientation _ order

/-- The genuine O52 edge charges and the corrected deletion order yield the
original `10 * mu` interior budget, with the canonical positioned partition. -/
theorem interior_total_le
    (graph : EndpointClosedEstimatingGraphData D eps Delta scaffold)
    {rho : ℕ} {mu lambda c : ℝ}
    (pieces : CellPieceData D eps Delta scaffold)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hmu : 0 ≤ mu) :
    (∑ i : Fin Delta.rCellCount,
      scaffold.partition.kindWeight Embedded.CellArcKind.interior i) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ) := by
  obtain ⟨order⟩ := graph.fiveDeletionOrder
  have hvertex : ∀ i : Fin Delta.rCellCount,
      0 ≤ ((Embedded.cell Delta i).word.length : ℝ) := by
    intro i
    positivity
  have hedge := edgeWeight_sum_le_of_fiveDeletionOrder order
    (2 * mu) (mul_nonneg (by norm_num) hmu)
    (fun i : Fin Delta.rCellCount =>
      ((Embedded.cell Delta i).word.length : ℝ))
    Embedded.InteriorEdge.weight hvertex
    (Embedded.InteriorEdge.weight_le_incident pieces.equations hcondition)
  have hsum := Embedded.sum_canonical_interiorWeight_eq_sum_edgeWeight
    scaffold.selected.family
    (Embedded.incidencePositionUnique_of_selfIncidenceSeparated
      scaffold.selected
      (Embedded.selfIncidenceSeparated_of_target_ne_source _))
  change (∑ i : Fin Delta.rCellCount,
      (Embedded.canonicalDiagramPartition scaffold.selected.family).kindWeight
        Embedded.CellArcKind.interior i) ≤ _
  rw [hsum]
  calc
    (∑ edge : Embedded.InteriorEdge scaffold.selected.family, edge.weight) ≤
        5 * (2 * mu) * ∑ i : Fin Delta.rCellCount,
          ((Embedded.cell Delta i).word.length : ℝ) := by
      simpa using hedge
    _ = _ := by ring

/-- Assemble the original embedded estimating system directly from corrected
graph data, O52, and the synchronized Lemma 62 output. No historical hereditary
graph certificate is constructed or consumed. -/
noncomputable def toEmbeddedEstimatingSystem
    (graph : EndpointClosedEstimatingGraphData D eps Delta scaffold)
    {rho : ℕ} {mu lambda c : ℝ}
    (pieces : CellPieceData D eps Delta scaffold)
    (unbound : Lemma62Data D eps mu rho Delta scaffold)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hrho : 0 < rho) (hcells : 0 < Delta.rCellCount)
    (hmu : 0 ≤ mu) : EmbeddedEstimatingSystem D eps mu Delta where
  selected := scaffold.selected
  partition := scaffold.partition
  outer := Embedded.selectedOuter scaffold.selected.family
  outerWeight_eq := Embedded.selectedOuter_weight_eq_canonicalExterior
    scaffold.selected
    (Embedded.selfIncidenceSeparated_of_target_ne_source _)
    (Embedded.exteriorRegionsUnique_of_mergeAvailable scaffold.selected
      graph.exteriorMergeAvailable)
  totalWeight_pos := by
    apply Finset.sum_pos
    · intro i _
      have hlong := hcondition.long (Embedded.cell Delta i).word
        (Embedded.cell Delta i).word_mem
      have hpos : 0 < (Embedded.cell Delta i).word.length := by omega
      exact_mod_cast hpos
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hcells)
  interior_total_le := graph.interior_total_le pieces hcondition hmu
  uncovered_total_le := by
    apply scaffold.partition.unbound_total_le_two_mu mu rho
    · intro i
      exact hcondition.long (Embedded.cell Delta i).word
        (Embedded.cell Delta i).word_mem
    · exact unbound.unbound_lt
    · exact unbound.threshold

end EndpointClosedEstimatingGraphData

/-- Joint geometric output on one O-equivalent diagram, at one pair of
parameters. Reducedness is retained so the proved local O52 construction
applies to exactly this scaffold. -/
def EstimatingJointConstructionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    (∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
      ∀ lambda c mu : ℝ,
        0 < lambda → lambda ≤ 1 → 0 ≤ c →
        0 < mu → mu ≤ 1 / 16 →
          ∃ eps rho : ℕ, 0 < rho ∧
            ∀ (W : Set (List (GGT.RelLetter G Lambda))),
              OsinCCondition D W eps mu lambda c rho →
                ∀ Delta : DiscDiagram.{u, w, v} W,
                  Delta.Reduced → 0 < Delta.rCellCount →
                  IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
                    ∃ Delta' : DiscDiagram.{u, w, v} W,
                      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
                        Delta'.Reduced ∧
                        ∃ scaffold : EstimatingScaffold D eps Delta',
                          Nonempty (EndpointClosedEstimatingGraphData
                            D eps Delta' scaffold) ∧
                          Nonempty (Lemma62Data D eps mu rho Delta' scaffold)

/-- The joint construction and local O52 prove the unchanged estimating
system construction statement. In particular, neither refuted historical
interface is an input to this reduction. -/
theorem embeddedEstimatingSystemConstruction_of_joint
    (hjoint : EstimatingJointConstructionStatement.{u, w, v})
    (hpieces : EstimatingPieceConstructionStatement.{u, w, v}) :
    EmbeddedEstimatingSystemConstructionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, hrho, hconstruction⟩ := hjoint D hhyper lambda c mu
    hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro W hcondition Delta hred hcells hboundary
  obtain ⟨Delta', ⟨equiv⟩, hred', scaffold, ⟨graph⟩, ⟨unbound⟩⟩ :=
    hconstruction W hcondition Delta hred hcells hboundary
  obtain ⟨pieces⟩ := hpieces D eps Delta' scaffold hred'
  have hcells' : 0 < Delta'.rCellCount := by
    rw [equiv.rCellCount_eq]
    exact hcells
  exact ⟨Delta', ⟨equiv⟩,
    ⟨graph.toEmbeddedEstimatingSystem pieces unbound hcondition hrho hcells'
      hmu.le⟩⟩

/-- The corrected joint geometry proves the original quasi-geodesic
Greendlinger proposition through the same strict `1 - 13 * mu` count. -/
theorem relativeGreendlingerQuasiGeodesic_of_joint
    (hjoint : EstimatingJointConstructionStatement.{u, w, v})
    (hpieces : EstimatingPieceConstructionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesic
    (embeddedEstimatingSystemConstruction_of_joint hjoint hpieces)

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.EndpointClosedEstimatingGraphData.fiveDeletionOrder
#audit_axioms GroupApproximation.GGT.VanKampen.EndpointClosedEstimatingGraphData.fiveOwnerOrientation
#audit_axioms GroupApproximation.GGT.VanKampen.EndpointClosedEstimatingGraphData.interior_total_le
#audit_axioms GroupApproximation.GGT.VanKampen.EndpointClosedEstimatingGraphData.toEmbeddedEstimatingSystem
#audit_axioms GroupApproximation.GGT.VanKampen.embeddedEstimatingSystemConstruction_of_joint
#audit_axioms GroupApproximation.GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_joint
