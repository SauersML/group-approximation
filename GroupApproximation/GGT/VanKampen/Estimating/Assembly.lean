import GroupApproximation.GGT.VanKampen.Estimating.Deletion
import GroupApproximation.GGT.VanKampen.Estimating.Incidence
import GroupApproximation.GGT.VanKampen.Estimating.Partition
import GroupApproximation.GGT.VanKampen.Estimating.Unbound
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

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
                        ∃ scaffold : EstimatingScaffold D eps Delta',
                          Nonempty (EstimatingGraphData D eps Delta' scaffold)

/-- The local O52 input: every selected face-set candidate has the two-cell
arc equations required by `PieceBridge`.  It is independent of the global
selection and unbound estimates. -/
def EstimatingPieceConstructionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W)
    (scaffold : EstimatingScaffold D eps Delta),
    Nonempty (CellPieceData D eps Delta scaffold)

/-- The local Lemmas `61` and `62` input: after selection, the unbound arc
partition satisfies the strict square-root budget and its numerical threshold.
The boundary quasi-geodesic is included so the source's unbound estimate is
not detached from the diagram hypotheses. -/
def EstimatingUnboundConstructionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ)
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
  obtain ⟨Delta', hequiv, scaffold, graph⟩ := hselect W hcondition Delta
    hred hcells hboundary
  obtain ⟨equiv⟩ := hequiv
  obtain ⟨graph⟩ := graph
  obtain ⟨pieces⟩ := hpieces D eps Delta' scaffold
  have hboundary' : IsLambdaCQuasiGeodesicWord D lambda c Delta'.boundaryWord := by
    rw [equiv.boundaryWord_eq]
    exact hboundary
  obtain ⟨unbound⟩ := hunbound D eps rho mu lambda c hcondition Delta'
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
  have hfalse : False := by simpa using hmem'
  exact hfalse.elim

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
    let equiv := Classical.choice hequiv
    have hcount : Delta.rCellCount = Delta'.rCellCount := by
      simpa only [Fintype.card_fin] using Fintype.card_congr equiv.cellIndex
    omega
  exact ⟨Delta', hequiv,
    ⟨data.toEmbeddedEstimatingSystem hcondition hrho hcells' (le_of_lt hmu)⟩⟩

/-- Thus the `EstimatingData` construction proves source-faithful Gr0. -/
theorem relativeGreendlingerQuasiGeodesic_of_data
    (hdata : EstimatingDataConstructionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicStatement.{u, w, v} :=
  relativeGreendlingerQuasiGeodesic
    (embeddedEstimatingSystemConstruction_of_data hdata)

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
