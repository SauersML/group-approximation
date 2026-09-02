import GroupApproximation.GGT.VanKampen.Estimating.Deletion
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

/-!
# Assembly of diagram estimating systems

This file assembles the geometric output of Osin's Appendix construction into
`EstimatingSystem`.  The input supplies the cellwise boundary partition, the
finite interior-contiguity edges, the hereditary planar edge bound for their
estimating graph, the local `2 * mu` edge estimate from Lemma O52, and the
unbound-arc budget from Lemmas 61 and 62.

The five-deletion order and the `10 * mu` interior budget are proved here, so
the geometric construction does not assume either global counting inequality
that `EstimatingSystem` needs.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w

/-- Geometric and local numerical data before the global estimating-system
count.  This is the output of the distinguished-family and unbound-arc
construction in Osin's Appendix. -/
structure EstimatingData
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (mu : ℝ) (Delta : DiscDiagram W) where
  outer : ∀ i : Fin Delta.rCellCount,
    Option (BoundaryContiguity (D := D) (eps := eps) (Delta.indexedCell i))
  interiorWeight : Fin Delta.rCellCount → ℝ
  uncoveredWeight : Fin Delta.rCellCount → ℝ
  interiorWeight_nonneg : ∀ i, 0 ≤ interiorWeight i
  uncoveredWeight_nonneg : ∀ i, 0 ≤ uncoveredWeight i
  partition : ∀ i,
    Delta.cellWeight i =
      (match outer i with
        | none => 0
        | some Gamma => (Gamma.region.secondArc.length : ℝ)) +
      interiorWeight i + uncoveredWeight i
  totalWeight_pos : 0 < ∑ i : Fin Delta.rCellCount, Delta.cellWeight i
  InteriorEdge : Type u
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
    edgeWeight edge ≤ 2 * mu * Delta.cellWeight i
  interiorWeight_sum :
    (∑ i : Fin Delta.rCellCount, interiorWeight i) =
      ∑ edge : InteriorEdge, edgeWeight edge
  uncovered_total_le :
    (∑ i : Fin Delta.rCellCount, uncoveredWeight i) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount, Delta.cellWeight i

attribute [instance] EstimatingData.interiorEdgeFintype
attribute [instance] EstimatingData.interiorEdgeDecidableEq
attribute [instance] EstimatingData.incidentDecidable

namespace EstimatingData

/-- The five-deletion order and the cell-to-cell piece estimate give Osin's
`10 * mu` global interior-contiguity budget. -/
theorem interior_total_le
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram W}
    (A : EstimatingData D eps mu Delta) (hmu : 0 ≤ mu) :
    (∑ i : Fin Delta.rCellCount, A.interiorWeight i) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount, Delta.cellWeight i := by
  have hfactor : 0 ≤ 2 * mu := mul_nonneg (by norm_num) hmu
  have hvertex : ∀ i : Fin Delta.rCellCount,
      0 ≤ Delta.cellWeight i := by
    intro i
    exact Nat.cast_nonneg _
  have haverage : HasHereditaryAverageDegreeLtSix A.incident :=
    hereditaryAverageDegree_of_planarEdgeBound A.incident
      A.atMostTwoEndpoints A.planarEdgeBound
  obtain ⟨order⟩ := exists_fiveDeletionOrder_of_hereditaryAverageDegree
    A.incident haverage Finset.univ Finset.univ A.edgesCovered
  have hedge := edgeWeight_sum_le_of_fiveDeletionOrder order
    (2 * mu) hfactor Delta.cellWeight A.edgeWeight hvertex
    A.edgeWeight_le_incident
  rw [A.interiorWeight_sum]
  calc
    (∑ edge : A.InteriorEdge, A.edgeWeight edge) ≤
        5 * (2 * mu) *
          ∑ i : Fin Delta.rCellCount, Delta.cellWeight i := by
      simpa using hedge
    _ = 10 * mu *
          ∑ i : Fin Delta.rCellCount, Delta.cellWeight i := by ring

/-- The local geometric data assemble into the estimating system used by the
relative Greendlinger count. -/
def toEstimatingSystem
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram W}
    (A : EstimatingData D eps mu Delta) (hmu : 0 ≤ mu) :
    EstimatingSystem D eps mu Delta where
  outer := A.outer
  interiorWeight := A.interiorWeight
  uncoveredWeight := A.uncoveredWeight
  interiorWeight_nonneg := A.interiorWeight_nonneg
  uncoveredWeight_nonneg := A.uncoveredWeight_nonneg
  partition := A.partition
  totalWeight_pos := A.totalWeight_pos
  interior_total_le := A.interior_total_le hmu
  uncovered_total_le := A.uncovered_total_le

end EstimatingData

/-! ## Statement-level assembly -/

/-- Constructing `EstimatingData` for every short reduced diagram proves the
named estimating-system statement.  The global `10 * mu` estimate is supplied
by `EstimatingData.interior_total_le`. -/
theorem estimatingSystemStatement_of_data
    (hdata : ∀ {G : Type u} [Group G] {Lambda : Type w}
      (D : GGT.RelGenSet G Lambda)
      (W : Set (List (GGT.RelLetter G Lambda)))
      (eps rho : ℕ) (mu : ℝ) (Delta : DiscDiagram W),
      RelWord.IsLemma44Input D W eps mu rho →
      0 < mu → mu ≤ 1 / 52 → 0 < rho →
      Delta.Reduced → 0 < Delta.rCellCount →
      Delta.boundaryWord.length < rho →
      Nonempty (EstimatingData D eps mu Delta)) :
    EstimatingSystemStatement.{u, w} := by
  intro G _ Lambda D W eps rho mu Delta hsc hmu hmuUpper hrho hred hcells
    hshort
  obtain ⟨A⟩ := hdata D W eps rho mu Delta hsc hmu hmuUpper hrho hred
    hcells hshort
  exact ⟨A.toEstimatingSystem (le_of_lt hmu)⟩

/-- Data selected uniformly from the hyperbolicity constant prove the named
estimating-system selection statement. -/
theorem estimatingSystemSelectionStatement_of_data
    (hdata : ∀ {G : Type u} [Group G] {Lambda : Type w}
      (D : GGT.RelGenSet G Lambda),
      D.IsHyperbolicallyEmbedded →
        ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
          ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
            ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
              RelWord.IsLemma44Input D W eps mu rho →
                ∀ (Z : HullSC.RelativeReducedDiagram D W R)
                  (C : RelativeDiscRealization Z),
                  Nonempty (EstimatingData D eps mu C.diagram)) :
    EstimatingSystemSelectionStatement.{u, w} := by
  intro G _ Lambda D hemb mu hmu hmuUpper
  obtain ⟨eps, rho0, hconstruction⟩ := hdata D hemb mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho W R hsc Z C
  obtain ⟨A⟩ := hconstruction rho hrho W R hsc Z C
  exact ⟨A.toEstimatingSystem (le_of_lt hmu)⟩

end VanKampen
end GGT
end GroupApproximation
