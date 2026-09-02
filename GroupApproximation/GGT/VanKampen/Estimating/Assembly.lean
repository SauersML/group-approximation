import GroupApproximation.GGT.VanKampen.Estimating.Deletion
import GroupApproximation.GGT.VanKampen.Estimating.Incidence
import GroupApproximation.GGT.VanKampen.Estimating.Partition
import GroupApproximation.GGT.VanKampen.Estimating.Unbound
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.VanKampen.Surgery

/-!
# Assembly of embedded estimating systems

This file assembles the geometric output of Osin's Appendix into the embedded
estimating system used by the strict Gr0 count.  Definition M and the cyclic
cell partition are retained in the data.  A hereditary planar incidence bound
produces the five-deletion order from Lemma Eul and so the global `10 * mu`
interior budget.  The unbound budget is the output of Lemmas 61 and 62.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w v

/-- The unconditional part of Appendix Definition M: a distinguished finite
family together with the canonical cyclic classification of every relator-cell
boundary dart. -/
structure EstimatingScaffold
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) where
  selected : EstimatingSelection.DistinguishedFamily
    (Embedded.Compatible (D := D) (eps := eps) (Delta := Delta))
    (Embedded.Candidate.weight (D := D) (eps := eps) (Delta := Delta))

namespace EstimatingScaffold

/-- The positioned boundary partition attached to a scaffold is the canonical
classifier of its distinguished family. -/
noncomputable def partition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (scaffold : EstimatingScaffold D eps Delta) :
    Embedded.DiagramBoundaryPartition scaffold.selected.family :=
  Embedded.canonicalDiagramPartition scaffold.selected.family

end EstimatingScaffold

/-- Finite maximization and canonical dart classification construct the
estimating scaffold for every finite disc diagram. -/
theorem exists_estimatingScaffold
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W) :
    Nonempty (EstimatingScaffold D eps Delta) := by
  obtain ⟨selected⟩ := Embedded.exists_distinguishedFamily D eps Delta
  exact ⟨{
    selected := selected }⟩

/-! ## Geometric certificates on the finite scaffold -/

/-- The conclusions of Appendix Lemma 65(a) needed by the estimating count.
The selected interior regions form a hereditary simple planar graph, no
position belongs to two incidences, and the two-gon condition leaves at most
one exterior region at each cell. -/
structure EstimatingGraphData
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta) where
  planarEdgeBound :
    HasHereditaryPlanarEdgeBound
      (Embedded.InteriorEdge.Incident
        (selected := scaffold.selected.family))
  selfIncidenceSeparated :
    Embedded.SelfIncidenceSeparated scaffold.selected.family
  exteriorMergeAvailable :
    Embedded.ExteriorMergeAvailable scaffold.selected.family

/-- Construct graph data from the three independent geometric certificates.
The certificates are exactly the hereditary planar inequality, the separated
incidence positions, and the admissible exterior merge supplied by the
estimating-graph surgery. -/
theorem estimatingGraphData_of_certificates
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (scaffold : EstimatingScaffold D eps Delta)
    (hplanar : HasHereditaryPlanarEdgeBound
      (Embedded.InteriorEdge.Incident
        (selected := scaffold.selected.family)))
    (hseparated : Embedded.SelfIncidenceSeparated scaffold.selected.family)
    (hmerge : Embedded.ExteriorMergeAvailable scaffold.selected.family) :
    Nonempty (EstimatingGraphData D eps Delta scaffold) := by
  exact ⟨{
    planarEdgeBound := hplanar
    selfIncidenceSeparated := hseparated
    exteriorMergeAvailable := hmerge }⟩

/-- The neutral surgery transports an already-certified scaffold to the
selection-output shape. This is the base case for the Lemma 65(a) surgery
induction. -/
theorem selectionOutput_of_graphData
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    (scaffold : EstimatingScaffold D eps Delta)
    (graph : Nonempty (EstimatingGraphData D eps Delta scaffold)) :
    ∃ Delta' : DiscDiagram.{u, w, v} W,
      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
        ∃ scaffold' : EstimatingScaffold D eps Delta',
          Nonempty (EstimatingGraphData D eps Delta' scaffold') := by
  refine ⟨Delta, ⟨OEquivalentDiscDiagram.refl Delta⟩, scaffold, graph⟩

/-- The G-cell boundary equation and reducedness exclusion needed to apply
Lemma O52 to every selected cell-to-cell region. -/
structure CellPieceData
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta) where
  equations : ∀ edge : Embedded.InteriorEdge scaffold.selected.family,
    Embedded.CellPieceEquations edge.candidate.contiguity

/-- The strict conclusion of Appendix Lemma 62 together with the final
large-`rho` numerical threshold. -/
structure Lemma62Data
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (mu : ℝ) (rho : ℕ)
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta) where
  unbound_lt : (scaffold.partition.unboundTotal : ℝ) <
    (Delta.rCellCount : ℝ) * Real.sqrt (rho : ℝ)
  threshold : 1 ≤ 2 * mu * Real.sqrt (rho : ℝ)

/-- Local geometric data before applying Lemma Eul. -/
structure EstimatingData
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (mu : ℝ) (Delta : DiscDiagram.{u, w, v} W) where
  selected : EstimatingSelection.DistinguishedFamily
    (Embedded.Compatible (D := D) (eps := eps) (Delta := Delta))
    (Embedded.Candidate.weight (D := D) (eps := eps) (Delta := Delta))
  partition : Embedded.DiagramBoundaryPartition selected.family
  outer : ∀ i : Fin Delta.rCellCount,
    Option (EmbeddedBoundaryContiguity D eps Delta i)
  outerWeight_eq : ∀ i : Fin Delta.rCellCount,
    (match outer i with
      | none => 0
      | some contiguity => contiguity.weight) =
        partition.kindWeight Embedded.CellArcKind.exterior i
  InteriorEdge : Type v
  interiorEdgeFintype : Fintype InteriorEdge
  interiorEdgeDecidableEq : DecidableEq InteriorEdge
  incident : Fin Delta.rCellCount → InteriorEdge → Prop
  incidentDecidable : DecidableRel incident
  edgesCovered :
    @EdgesCovered (Fin Delta.rCellCount) InteriorEdge
      incident Finset.univ Finset.univ
  atMostTwoEndpoints :
    @HasAtMostTwoEndpoints (Fin Delta.rCellCount) InteriorEdge
      (inferInstance) incident incidentDecidable
  planarEdgeBound :
    @HasHereditaryPlanarEdgeBound (Fin Delta.rCellCount) InteriorEdge
      (inferInstance) interiorEdgeDecidableEq incident incidentDecidable
  edgeWeight : InteriorEdge → ℝ
  edgeWeight_le_incident : ∀ i edge, incident i edge →
    edgeWeight edge ≤
      2 * mu * ((Embedded.cell Delta i).word.length : ℝ)
  interiorWeight_sum :
    (∑ i : Fin Delta.rCellCount,
        partition.kindWeight Embedded.CellArcKind.interior i) =
      ∑ edge : InteriorEdge, edgeWeight edge
  uncovered_total_le :
    (∑ i : Fin Delta.rCellCount,
        partition.kindWeight Embedded.CellArcKind.unbound i) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ)

attribute [instance] EstimatingData.interiorEdgeFintype
attribute [instance] EstimatingData.interiorEdgeDecidableEq
attribute [instance] EstimatingData.incidentDecidable

namespace EstimatingData

/-- Assemble `EstimatingData` from the exact geometric conclusions of Lemma
65(a), O52, and Lemma 62.  Coverage, endpoint count, and both endpoint charges
are supplied by the canonical interior-incidence graph. -/
noncomputable def ofScaffold
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    (scaffold : EstimatingScaffold D eps Delta)
    (graph : EstimatingGraphData D eps Delta scaffold)
    (pieces : CellPieceData D eps Delta scaffold)
    (unbound : Lemma62Data D eps mu rho Delta scaffold)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    EstimatingData D eps mu Delta where
  selected := scaffold.selected
  partition := scaffold.partition
  outer := Embedded.selectedOuter scaffold.selected.family
  outerWeight_eq := Embedded.selectedOuter_weight_eq_canonicalExterior
    scaffold.selected graph.selfIncidenceSeparated
      (Embedded.exteriorRegionsUnique_of_mergeAvailable scaffold.selected
        graph.exteriorMergeAvailable)
  InteriorEdge := Embedded.InteriorEdge scaffold.selected.family
  interiorEdgeFintype := inferInstance
  interiorEdgeDecidableEq := inferInstance
  incident := Embedded.InteriorEdge.Incident
  incidentDecidable := inferInstance
  edgesCovered := Embedded.InteriorEdge.edgesCovered_univ
  atMostTwoEndpoints := Embedded.InteriorEdge.hasAtMostTwoEndpoints
  planarEdgeBound := graph.planarEdgeBound
  edgeWeight := Embedded.InteriorEdge.weight
  edgeWeight_le_incident := by
    intro i edge hincident
    change Embedded.InteriorEdge.Incident i edge at hincident
    exact Embedded.InteriorEdge.weight_le_incident pieces.equations
      hcondition i edge hincident
  interiorWeight_sum := by
    change (∑ i : Fin Delta.rCellCount,
        (Embedded.canonicalDiagramPartition scaffold.selected.family).kindWeight
          Embedded.CellArcKind.interior i) =
      ∑ edge : Embedded.InteriorEdge scaffold.selected.family, edge.weight
    exact Embedded.sum_canonical_interiorWeight_eq_sum_edgeWeight
      scaffold.selected.family
      (Embedded.incidencePositionUnique_of_selfIncidenceSeparated
        scaffold.selected graph.selfIncidenceSeparated)
  uncovered_total_le := by
    apply scaffold.partition.unbound_total_le_two_mu mu rho
    · intro i
      exact hcondition.long (Embedded.cell Delta i).word
        (Embedded.cell Delta i).word_mem
    · exact unbound.unbound_lt
    · exact unbound.threshold

/-- The three source-level certificates give the requested inhabited
`EstimatingData` object. -/
theorem nonempty_of_certificates
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    (scaffold : EstimatingScaffold D eps Delta)
    (graph : EstimatingGraphData D eps Delta scaffold)
    (pieces : CellPieceData D eps Delta scaffold)
    (unbound : Lemma62Data D eps mu rho Delta scaffold)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    Nonempty (EstimatingData D eps mu Delta) :=
  ⟨ofScaffold scaffold graph pieces unbound hcondition⟩

/-- Lemma Eul gives the `10 * mu` total interior-contiguity budget. -/
theorem interior_total_le
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    (data : EstimatingData D eps mu Delta) (hmu : 0 ≤ mu) :
    (∑ i : Fin Delta.rCellCount,
        data.partition.kindWeight Embedded.CellArcKind.interior i) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ) := by
  have hfactor : 0 ≤ 2 * mu := mul_nonneg (by norm_num) hmu
  have hvertex : ∀ i : Fin Delta.rCellCount,
      0 ≤ ((Embedded.cell Delta i).word.length : ℝ) := by
    intro i
    positivity
  have haverage : HasHereditaryAverageDegreeLtSix data.incident :=
    hereditaryAverageDegree_of_planarEdgeBound data.incident
      data.atMostTwoEndpoints data.planarEdgeBound
  obtain ⟨order⟩ := exists_fiveDeletionOrder_of_hereditaryAverageDegree
    data.incident haverage Finset.univ Finset.univ data.edgesCovered
  have hedge := edgeWeight_sum_le_of_fiveDeletionOrder order
    (2 * mu) hfactor
    (fun i : Fin Delta.rCellCount =>
      ((Embedded.cell Delta i).word.length : ℝ))
    data.edgeWeight hvertex data.edgeWeight_le_incident
  rw [data.interiorWeight_sum]
  calc
    (∑ edge : data.InteriorEdge, data.edgeWeight edge) ≤
        5 * (2 * mu) * ∑ i : Fin Delta.rCellCount,
          ((Embedded.cell Delta i).word.length : ℝ) := by
      simpa using hedge
    _ = 10 * mu * ∑ i : Fin Delta.rCellCount,
          ((Embedded.cell Delta i).word.length : ℝ) := by ring

/-- The hereditary planar incidence certificate yields the explicit
five-owner orientation of Osin's Appendix Lemma `Eul`. -/
theorem fiveOwnerOrientation
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    (data : EstimatingData D eps mu Delta)
    (hcells : 0 < Delta.rCellCount) :
    Nonempty (FiveOwnerOrientation data.incident
      (Finset.univ : Finset (Fin Delta.rCellCount))
      (Finset.univ : Finset data.InteriorEdge)) := by
  have haverage : HasHereditaryAverageDegreeLtSix data.incident :=
    hereditaryAverageDegree_of_planarEdgeBound data.incident
      data.atMostTwoEndpoints data.planarEdgeBound
  obtain ⟨order⟩ := exists_fiveDeletionOrder_of_hereditaryAverageDegree
    data.incident haverage Finset.univ Finset.univ data.edgesCovered
  letI : Nonempty (Fin Delta.rCellCount) :=
    Fin.pos_iff_nonempty.mp hcells
  exact FiveDeletionOrder.toOwnerOrientation data.incident order

/-- Positive cell count and the positive source threshold make total relator
perimeter positive. -/
theorem totalWeight_pos
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    (_data : EstimatingData D eps mu Delta)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hrho : 0 < rho) (hcells : 0 < Delta.rCellCount) :
    0 < ∑ i : Fin Delta.rCellCount,
      ((Embedded.cell Delta i).word.length : ℝ) := by
  have hnonempty : Nonempty (Fin Delta.rCellCount) :=
    Fin.pos_iff_nonempty.mp hcells
  apply Finset.sum_pos
  · intro i _
    have hlong : rho ≤ (Embedded.cell Delta i).word.length :=
      hcondition.long (Embedded.cell Delta i).word
        (Embedded.cell Delta i).word_mem
    have hpositive : 0 < (Embedded.cell Delta i).word.length := by omega
    exact_mod_cast hpositive
  · exact Finset.univ_nonempty_iff.mpr hnonempty

/-- Assemble the final embedded estimating system. -/
def toEmbeddedEstimatingSystem
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    (data : EstimatingData D eps mu Delta)
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hrho : 0 < rho) (hcells : 0 < Delta.rCellCount)
    (hmu : 0 ≤ mu) : EmbeddedEstimatingSystem D eps mu Delta where
  selected := data.selected
  partition := data.partition
  outer := data.outer
  outerWeight_eq := data.outerWeight_eq
  totalWeight_pos := data.totalWeight_pos hcondition hrho hcells
  interior_total_le := data.interior_total_le hmu
  uncovered_total_le := data.uncovered_total_le

end EstimatingData

/-! ## Construction statement -/

/-- The remaining geometric construction at the `EstimatingData` level.  Its
fields are exactly Lemma 65(a), the estimating-graph planarity input to Lemma
Eul, the O52 local edge bounds, and Lemma 62's unbound budget. -/
def EstimatingDataConstructionStatement : Prop :=
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
                        Nonempty (EstimatingData D eps mu Delta')

/-- The selection and Lemma `65(a)` input, separated from the local O52 and
unbound estimates.  It chooses the `O`-equivalent diagram, the finite
Definition-`M` scaffold, and the hereditary estimating-graph certificates. -/
def EstimatingSelectionConstructionStatement : Prop :=
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
                          Nonempty (EstimatingGraphData D eps Delta' scaffold)

/-- A local Lemma 65(a) face-drop oracle either already supplies the simple
estimating graph or gives an O-equivalent reduced diagram with strictly fewer
ambient faces.  The measure is the area of the planar face decomposition. -/
def SelectionFaceDropOracle
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (_hcondition : OsinCCondition D W eps mu lambda c rho) : Prop :=
  ∀ (Delta : DiscDiagram.{u, w, v} W),
    Delta.Reduced → 0 < Delta.rCellCount →
      IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      (∃ scaffold : EstimatingScaffold D eps Delta,
        Nonempty (EstimatingGraphData D eps Delta scaffold)) ∨
      ∃ Delta' : DiscDiagram.{u, w, v} W,
        Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
          Delta'.toCombMap.faceCount < Delta.toCombMap.faceCount ∧
          Delta'.Reduced ∧ 0 < Delta'.rCellCount ∧
            IsLambdaCQuasiGeodesicWord D lambda c Delta'.boundaryWord

/-! ## Retyping the map-level region replacement -/

/-- The relator-cell equivalence carried by a `GRegionReplacement` is the
`O`-equivalence required by the estimating selection statement.  Its index
map is the finite cast supplied by the ordered relator-cell equivalence, and
the word field follows by taking the corresponding entry of the transported
cell list. -/
def OEquivalentDiscDiagram.ofGRegionReplacement
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (replacement : Surgery.GRegionReplacement Delta) :
    OEquivalentDiscDiagram Delta replacement.diagram := by
  let cells := replacement.cells
  refine {
    boundaryWord_eq := replacement.outerWord_eq
    cellIndex := cells.indexEquiv
    cellWord_eq := ?_ }
  intro i
  have hlist : replacement.diagram.relatorCells =
      Delta.relatorCells.map cells.cellEquiv := cells.cells_eq
  have hword := cells.word_eq (Delta.relatorCells.get i)
  have hget : replacement.diagram.relatorCells.get (cells.indexEquiv i) =
      cells.cellEquiv (Delta.relatorCells.get i) := by
    simp only [List.get_eq_getElem, hlist, List.getElem_map]
    rfl
  change (replacement.diagram.relatorCells.get (cells.indexEquiv i)).word =
    (Delta.relatorCells.get i).word
  rw [hget, hword]

/-- A map-level region replacement with a strict face-count drop supplies the
drop branch of the Lemma 65(a) face-drop oracle.  The relator count, reducedness,
and boundary quasi-geodesicity are transported by the replacement certificate. -/
theorem selection_drop_of_gRegionReplacement
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {lambda c : ℝ}
    {Delta : DiscDiagram.{u, w, v} W}
    (hred : Delta.Reduced)
    (hcells : 0 < Delta.rCellCount)
    (hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord)
    (replacement : Surgery.GRegionReplacement.{u, w, v, v} Delta)
    (hdrop : replacement.diagram.toCombMap.faceCount <
      Delta.toCombMap.faceCount) :
    ∃ Delta' : DiscDiagram.{u, w, v} W,
      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
        Delta'.toCombMap.faceCount < Delta.toCombMap.faceCount ∧
        Delta'.Reduced ∧ 0 < Delta'.rCellCount ∧
          IsLambdaCQuasiGeodesicWord D lambda c Delta'.boundaryWord := by
  let Delta' := replacement.diagram
  let equiv : OEquivalentDiscDiagram Delta Delta' :=
    OEquivalentDiscDiagram.ofGRegionReplacement replacement
  have hred' : Delta'.Reduced := replacement.reduced hred
  have hcount' : Delta'.rCellCount = Delta.rCellCount :=
    replacement.rCellCount_eq
  have hcells' : 0 < Delta'.rCellCount := by
    rw [hcount']
    exact hcells
  have hboundary' : IsLambdaCQuasiGeodesicWord D lambda c Delta'.boundaryWord :=
    equiv.boundary_quasiGeodesic hboundary
  exact ⟨Delta', ⟨equiv⟩, hdrop, hred', hcells', hboundary'⟩

/-- A per-diagram terminal certificate or map-level replacement is exactly a
face-drop oracle.  The replacement branch is retyped by
`selection_drop_of_gRegionReplacement`, so all fields required by Lemma
65(a) are checked at this boundary. -/
theorem selectionFaceDropOracle_of_gRegionReplacements
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (hreplacement : ∀ (Delta : DiscDiagram.{u, w, v} W),
      Delta.Reduced → 0 < Delta.rCellCount →
      IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      (∃ scaffold : EstimatingScaffold D eps Delta,
        Nonempty (EstimatingGraphData D eps Delta scaffold)) ∨
      ∃ replacement : Surgery.GRegionReplacement.{u, w, v, v} Delta,
        replacement.diagram.toCombMap.faceCount <
          Delta.toCombMap.faceCount) :
    SelectionFaceDropOracle.{u, w, v} D eps rho mu lambda c hcondition := by
  intro Delta hred hcells hboundary
  rcases hreplacement Delta hred hcells hboundary with hterminal | hdrop
  · exact Or.inl hterminal
  · obtain ⟨replacement, hface⟩ := hdrop
    exact Or.inr (selection_drop_of_gRegionReplacement hred hcells hboundary
      replacement hface)

/-- O-equivalence composes, so successive face-drop surgeries retain the
boundary word and ordered relator-cell words. -/
def OEquivalentDiscDiagram.trans
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta₁ Delta₂ Delta₃ : DiscDiagram.{u, w, v} W}
    (first : OEquivalentDiscDiagram Delta₁ Delta₂)
    (second : OEquivalentDiscDiagram Delta₂ Delta₃) :
    OEquivalentDiscDiagram Delta₁ Delta₃ where
  boundaryWord_eq := second.boundaryWord_eq.trans first.boundaryWord_eq
  cellIndex := first.cellIndex.trans second.cellIndex
  cellWord_eq := by
    intro i
    calc
      (Embedded.cell Delta₃ (first.cellIndex.trans second.cellIndex i)).word =
          (Embedded.cell Delta₂ (first.cellIndex i)).word :=
        second.cellWord_eq (first.cellIndex i)
      _ = (Embedded.cell Delta₁ i).word := first.cellWord_eq i

/-- Strong induction on ambient face count turns the local face-drop oracle
into the fixed-diagram output required by Lemma 65(a). -/
theorem selection_output_of_faceDropOracle
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (oracle : SelectionFaceDropOracle.{u, w, v} D eps rho mu lambda c hcondition)
    (Delta : DiscDiagram.{u, w, v} W)
    (hred : Delta.Reduced) (hcells : 0 < Delta.rCellCount)
    (hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord) :
      ∃ Delta' : DiscDiagram.{u, w, v} W,
      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
        Delta'.Reduced ∧
        ∃ scaffold : EstimatingScaffold D eps Delta',
          Nonempty (EstimatingGraphData D eps Delta' scaffold) := by
  have aux : ∀ n : ℕ, ∀ (Delta : DiscDiagram.{u, w, v} W),
      Delta.toCombMap.faceCount = n → Delta.Reduced →
        0 < Delta.rCellCount →
          IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
            ∃ Delta' : DiscDiagram.{u, w, v} W,
              Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
                Delta'.Reduced ∧
                ∃ scaffold : EstimatingScaffold D eps Delta',
                  Nonempty (EstimatingGraphData D eps Delta' scaffold) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Delta hface hred' hcells' hboundary'
        rcases oracle Delta hred' hcells' hboundary' with hterminal | hdrop
        · rcases hterminal with ⟨scaffold, graph⟩
          exact ⟨Delta, ⟨OEquivalentDiscDiagram.refl Delta⟩, hred', scaffold, graph⟩
        · obtain ⟨Delta₂, hequiv, hdropFace, hred₂, hcells₂, hboundary₂⟩ := hdrop
          obtain ⟨equiv₁⟩ := hequiv
          have hlt : Delta₂.toCombMap.faceCount < n := by
            omega
          obtain ⟨Delta₃, hequiv₂, hred₃, scaffold, graph⟩ :=
            ih Delta₂.toCombMap.faceCount hlt Delta₂ rfl hred₂ hcells₂ hboundary₂
          obtain ⟨equiv₂⟩ := hequiv₂
          exact ⟨Delta₃, ⟨equiv₁.trans equiv₂⟩, hred₃, scaffold, graph⟩
  exact aux Delta.toCombMap.faceCount Delta rfl hred hcells hboundary

/-! The preceding induction is the complete finite part of Lemma 65(a).  The
remaining geometric input is therefore packaged once, at the exact outer
quantifiers of the construction statement. -/

theorem estimatingSelectionConstruction_of_faceDropOracles
    (hparameter :
      ∀ {G : Type u} [Group G] {Lambda : Type w}
        (D : GGT.RelGenSet G Lambda),
        (∃ delta : ℕ,
          Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
        ∀ lambda c mu : ℝ,
          0 < lambda → lambda ≤ 1 → 0 ≤ c →
          0 < mu → mu ≤ 1 / 16 →
          ∃ eps rho : ℕ, 0 < rho ∧
            ∀ (W : Set (List (GGT.RelLetter G Lambda))),
              ∀ hcondition : OsinCCondition D W eps mu lambda c rho,
                SelectionFaceDropOracle.{u, w, v} D eps rho mu lambda c hcondition) :
    EstimatingSelectionConstructionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, hrho, horacle⟩ := hparameter D hhyper lambda c mu
    hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro W hcondition Delta hred hcells hboundary
  exact selection_output_of_faceDropOracle D eps rho mu lambda c hcondition
    (horacle W hcondition) Delta hred hcells hboundary

/-- The local O52 input: every selected face-set candidate has the two-cell
arc equations required by `PieceBridge`.  It is independent of the global
selection and unbound estimates. -/
def EstimatingPieceConstructionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta),
    Delta.Reduced →
    Nonempty (CellPieceData D eps Delta scaffold)

/-! ## Local piece-construction bridge -/

/-- Pasted face-set homotopies and reducedness bridges construct all local
O52 equations on a fixed scaffold. This exposes the finite per-edge
certificates required by the topological peeling proof. -/
theorem estimatingPieceConstruction_of_pasting_reduced
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta)
    (hred : Delta.Reduced)
    (hcertificate : ∀ edge : Embedded.InteriorEdge scaffold.selected.family,
      Embedded.PastingReducedCellPieceCertificate edge.candidate.contiguity) :
    Nonempty (CellPieceData D eps Delta scaffold) := by
  refine ⟨{ equations := ?_ }⟩
  intro edge
  exact (hcertificate edge).equations hred

/-- Boundary peeling schedules and reduced cell bridges construct the complete
piece certificate for every selected interior edge.  The schedule's
`BoundaryStep` moves account for each boundary dart, while
`CellPieceEquations.of_boundaryPeeling` performs the resulting word-value
calculation. -/
theorem estimatingPieceConstruction_of_boundaryPeelings
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta)
    (hred : Delta.Reduced)
    (hbridge : ∀ edge : Embedded.InteriorEdge scaffold.selected.family,
      Embedded.ReducedCellPieceBridge edge.candidate.contiguity)
    (hpeeling : ∀ edge : Embedded.InteriorEdge scaffold.selected.family,
      Embedded.FaceSetBoundaryPeeling edge.candidate.contiguity.boundary) :
    Nonempty (CellPieceData D eps Delta scaffold) := by
  refine ⟨{ equations := ?_ }⟩
  intro edge
  exact Embedded.CellPieceEquations.of_boundaryPeeling
    (hbridge edge) (hpeeling edge) hred

/-/ The direct boundary-counting form of the Piece construction.  This is the
exact callback produced by counting boundary darts of each selected region;
the reduced bridge contributes only the non-cancellation inequality. -/
theorem estimatingPieceConstruction_of_boundaryEquations
    (hbridge :
      ∀ {G : Type u} [Group G] {Lambda : Type w}
        (D : GGT.RelGenSet G Lambda) (eps : ℕ)
        {W : Set (List (GGT.RelLetter G Lambda))}
        (Delta : DiscDiagram.{u, w, v} W)
        (scaffold : EstimatingScaffold D eps Delta)
        (_hred : Delta.Reduced)
        (edge : Embedded.InteriorEdge scaffold.selected.family),
        Embedded.ReducedCellPieceBridge edge.candidate.contiguity)
    (harcs :
      ∀ {G : Type u} [Group G] {Lambda : Type w}
        {W : Set (List (GGT.RelLetter G Lambda))}
        {Delta : DiscDiagram.{u, w, v} W}
        {D : GGT.RelGenSet G Lambda} {eps : ℕ}
        (scaffold : EstimatingScaffold D eps Delta)
        (edge : Embedded.InteriorEdge scaffold.selected.family),
        GGT.RelLetter.listVal
            (Embedded.dartWord Delta
              (Embedded.targetBoundaryDarts Delta
                edge.candidate.contiguity.target
                edge.candidate.contiguity.targetArc)) =
          (GGT.RelLetter.listVal
              (Embedded.dartWord Delta edge.candidate.contiguity.rightSide))⁻¹ *
            GGT.RelLetter.listVal
              (Embedded.dartWord Delta edge.candidate.contiguity.sourceArc.darts) *
            (GGT.RelLetter.listVal
              (Embedded.dartWord Delta edge.candidate.contiguity.leftSide))⁻¹) :
    EstimatingPieceConstructionStatement.{u, w, v} := by
  intro G _ Lambda D eps W Delta scaffold hred
  refine ⟨{ equations := ?_ }⟩
  intro edge
  let bridge := hbridge D eps Delta scaffold hred edge
  exact Embedded.CellPieceEquations.of_boundary_equation_reduced
    edge.candidate.contiguity bridge (harcs scaffold edge) hred

/-- The one-step planar peel callback and the reduced cell bridge are exactly
the remaining producers for the global Piece construction statement.  The
face-count induction is supplied by `faceSetBoundaryPeeling_of_planarCertificates`,
and the resulting homotopy is consumed by `CellPieceEquations.of_boundaryPeeling`.
-/
theorem estimatingPieceConstruction_of_planarPeelOracle
    (hbridge :
      ∀ {G : Type u} [Group G] {Lambda : Type w}
        (D : GGT.RelGenSet G Lambda) (eps : ℕ)
        {W : Set (List (GGT.RelLetter G Lambda))}
        (Delta : DiscDiagram.{u, w, v} W)
        (scaffold : EstimatingScaffold D eps Delta)
        (_hred : Delta.Reduced)
        (edge : Embedded.InteriorEdge scaffold.selected.family),
        Embedded.ReducedCellPieceBridge edge.candidate.contiguity)
    (hplanar :
      ∀ {G : Type u} [Group G] {Lambda : Type w}
        {W : Set (List (GGT.RelLetter G Lambda))}
        {Delta : DiscDiagram.{u, w, v} W}
        {faces : Finset Delta.toCombMap.Face}
        (boundary : Embedded.FaceSetBoundary Delta faces),
        Embedded.PlanarFacePeelCertificate boundary) :
    EstimatingPieceConstructionStatement.{u, w, v} := by
  refine estimatingPieceConstruction_of_boundaryEquations hbridge ?_
  intro G _ Lambda W Delta D eps scaffold edge
  let peeling : Embedded.FaceSetBoundaryPeeling
      edge.candidate.contiguity.boundary :=
    Embedded.faceSetBoundaryPeeling_of_planarCertificates
      edge.candidate.contiguity.boundary (fun boundary => hplanar boundary)
  exact edge.candidate.contiguity.targetBoundary_value_of_pasting
    peeling.to_homotopy

/-- The local Lemmas `61` and `62` input: after selection, the unbound arc
partition satisfies the strict square-root budget and its numerical threshold.
The boundary quasi-geodesic is included so the source's unbound estimate is
not detached from the diagram hypotheses. -/
def EstimatingUnboundConstructionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    (_hrho : 0 < rho)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (_hcondition : OsinCCondition D W eps mu lambda c rho)
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta),
    IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
      Nonempty (Lemma62Data D eps mu rho Delta scaffold)

/-- The three source-level certificates assemble into the complete geometric
construction used by the strict Gr0 count. -/
theorem estimatingDataConstruction_of_components
    (hselection : EstimatingSelectionConstructionStatement.{u, w, v})
    (hpieces : EstimatingPieceConstructionStatement.{u, w, v})
    (hunbound : EstimatingUnboundConstructionStatement.{u, w, v}) :
    EstimatingDataConstructionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, hrho, hselect⟩ := hselection D hhyper lambda c mu
    hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro W hcondition Delta hred hcells hboundary
  obtain ⟨Delta', hequiv, hred', scaffold, graph⟩ := hselect W hcondition Delta
    hred hcells hboundary
  obtain ⟨equiv⟩ := hequiv
  obtain ⟨graph⟩ := graph
  obtain ⟨pieces⟩ := hpieces D eps Delta' scaffold hred'
  have hboundary' : IsLambdaCQuasiGeodesicWord D lambda c Delta'.boundaryWord :=
    equiv.boundary_quasiGeodesic hboundary
  obtain ⟨unbound⟩ := hunbound D eps rho mu lambda c hrho hcondition Delta'
    scaffold hboundary'
  exact ⟨Delta', ⟨equiv⟩,
    EstimatingData.nonempty_of_certificates scaffold graph pieces unbound
      hcondition⟩

/-! ## Component model checks -/

/-- No positive relator-cell diagram exists over the empty word family. -/
theorem no_positive_rCells_emptyFamily
    {G : Type u} [Group G] {Lambda : Type w}
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda)))) :
    ¬ 0 < Delta.rCellCount := by
  intro hpos
  rw [DiscDiagram.rCellCount, List.length_pos_iff] at hpos
  obtain ⟨C, cells, hsplit⟩ := List.exists_cons_of_ne_nil hpos
  have hmem : C ∈ Delta.relatorCells := by
    rw [hsplit]
    exact List.mem_cons_self
  have hempty : C.word ∈
      (∅ : Set (List (GGT.RelLetter G Lambda))) := C.word_mem
  exact (Set.mem_empty_iff_false C.word).mp hempty

/-- The face-drop oracle has a vacuous empty-family model: its positive-cell
branch cannot occur, so the oracle conclusion follows by elimination. -/
theorem selectionFaceDropOracle_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (hWempty : W = ∅)
    (hcondition : OsinCCondition D W eps mu lambda c rho) :
    SelectionFaceDropOracle D eps rho mu lambda c hcondition := by
  intro Delta hred hcells hboundary
  have hrelators : Delta.relatorCells = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro cell _hmem
    have hword : cell.word ∈ (∅ : Set (List (GGT.RelLetter G Lambda))) := by
      rw [← hWempty]
      exact cell.word_mem
    exact (Set.mem_empty_iff_false cell.word).mp hword
  have hcount : Delta.rCellCount = 0 := by
    rw [DiscDiagram.rCellCount, hrelators]
    rfl
  omega

/-- The local O52 component is inhabited in the empty selected-family model:
the edge equation field is vacuous. -/
theorem estimatingPieceConstruction_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta)
    (hempty : scaffold.selected.family = ∅) :
    Nonempty (CellPieceData D eps Delta scaffold) := by
  refine ⟨{ equations := ?_ }⟩
  intro edge
  have hmem : edge.candidate ∈ scaffold.selected.family :=
    edge.candidate_mem
  have hmem' : edge.candidate ∈
      (∅ : Finset (Embedded.Candidate D eps Delta)) := hempty ▸ hmem
  simp at hmem'

/-- The selection component is vacuous on the empty family whenever the
positive-cell diagram hypothesis is supplied. -/
theorem estimatingSelectionConstruction_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda))))
    (_hcondition : OsinCCondition D (∅ : Set (List (GGT.RelLetter G Lambda)))
      eps mu lambda c rho)
    (_hred : Delta.Reduced) (hcells : 0 < Delta.rCellCount)
    (_hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord) :
    ∃ Delta' : DiscDiagram.{u, w, v}
        (∅ : Set (List (GGT.RelLetter G Lambda))),
      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
        ∃ scaffold : EstimatingScaffold D eps Delta',
          Nonempty (EstimatingGraphData D eps Delta' scaffold) := by
  exact (no_positive_rCells_emptyFamily Delta hcells).elim

/-! The graph certificate itself has a concrete degenerate model. -/

/-- The estimating graph fields are inhabited when the selected family is
empty: there are no interior edges, no loop incidences, and no exterior
two-region pairs. -/
theorem estimatingGraphData_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta)
    (hempty : scaffold.selected.family = ∅) :
    Nonempty (EstimatingGraphData D eps Delta scaffold) := by
  have hedge_empty : ∀ edges : Finset
      (Embedded.InteriorEdge scaffold.selected.family), edges = ∅ := by
    intro edges
    ext edge
    constructor
    · intro hedge
      have hcandidate : edge.candidate ∈ scaffold.selected.family :=
        edge.candidate_mem
      have hcandidate' : edge.candidate ∈
          (∅ : Finset (Embedded.Candidate D eps Delta)) :=
        hempty ▸ hcandidate
      simp at hcandidate'
    · intro hedge
      simp at hedge
  refine ⟨{
    planarEdgeBound := ?_
    selfIncidenceSeparated := ?_
    exteriorMergeAvailable := ?_ }⟩
  · intro vertices edges _hcovered _hvertices
    have hedge : edges = ∅ := hedge_empty edges
    rw [hedge]
    simp
  · rw [hempty]
    exact Embedded.selfIncidenceSeparated_emptyModel
  · rw [hempty]
    exact Embedded.exteriorMergeAvailable_emptyModel

/-- The unbound component is vacuous on the empty family whenever the
positive-cell diagram hypothesis is supplied. -/
theorem estimatingUnboundConstruction_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda))))
    (_hcondition : OsinCCondition D (∅ : Set (List (GGT.RelLetter G Lambda)))
      eps mu lambda c rho)
    (scaffold : EstimatingScaffold D eps Delta)
    (_hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord)
    (hcells : 0 < Delta.rCellCount) :
    Nonempty (Lemma62Data D eps mu rho Delta scaffold) := by
  exact (no_positive_rCells_emptyFamily Delta hcells).elim

/-- `EstimatingData` proves the embedded construction statement. -/
theorem embeddedEstimatingSystemConstruction_of_data
    (hdata : EstimatingDataConstructionStatement.{u, w, v}) :
    EmbeddedEstimatingSystemConstructionStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, hrho, hconstruction⟩ := hdata D hhyper lambda c mu
    hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro W hcondition Delta hred hcells hboundary
  obtain ⟨Delta', hequiv, data⟩ :=
    hconstruction W hcondition Delta hred hcells hboundary
  obtain ⟨data⟩ := data
  have hcells' : 0 < Delta'.rCellCount := by
    obtain ⟨equiv⟩ := hequiv
    have hcount : Delta'.rCellCount = Delta.rCellCount :=
      equiv.rCellCount_eq
    omega
  exact ⟨Delta', hequiv,
    ⟨data.toEmbeddedEstimatingSystem hcondition hrho hcells' (le_of_lt hmu)⟩⟩

/-- Thus the `EstimatingData` construction proves source-faithful Gr0. -/
theorem relativeGreendlingerQuasiGeodesic_of_data
    (hdata : EstimatingDataConstructionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesic
    (embeddedEstimatingSystemConstruction_of_data hdata)

/-- The separated selection, O52, and unbound certificates prove the
source-faithful quasi-geodesic Gr0 statement directly. -/
theorem relativeGreendlingerQuasiGeodesic_of_components
    (hselection : EstimatingSelectionConstructionStatement.{u, w, v})
    (hpieces : EstimatingPieceConstructionStatement.{u, w, v})
    (hunbound : EstimatingUnboundConstructionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesic_of_data
    (estimatingDataConstruction_of_components hselection hpieces hunbound)

/-- The `EstimatingData` construction conclusion over the empty relator
family is valid because its positive-cell hypothesis is impossible. -/
theorem estimatingDataConstruction_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ) (mu _lambda _c : ℝ)
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda))))
    (hcells : 0 < Delta.rCellCount) :
    ∃ Delta' : DiscDiagram.{u, w, v}
        (∅ : Set (List (GGT.RelLetter G Lambda))),
      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
        Nonempty (EstimatingData D eps mu Delta') := by
  exact False.elim
    (embeddedEstimatingSystemConstruction_emptyFamilyModel D Delta hcells)

end VanKampen
end GGT
end GroupApproximation
