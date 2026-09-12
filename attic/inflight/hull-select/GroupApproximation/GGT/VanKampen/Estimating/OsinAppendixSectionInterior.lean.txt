import GroupApproximation.GGT.VanKampen.Estimating.RegionPartition
import GroupApproximation.GGT.VanKampen.Estimating.EndpointClosedDeletion
import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSectionPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# The interior budget of Lemma 9.5 on actual region families

Osin, arXiv:math/0411039v3, Lemma 9.5: "By Lemma 4.3, `ν(e) ≤ 2μν(o)` whenever
`o` and `e` are incident.  Hence `Σ_inn ≤ 10μΣ` by Lemma 9.1 and `(∗)`."  Here
`Φ_M` has the relator cells as vertices and the selected cell-to-cell regions as
edges; an edge has weight the sum of its two contiguity arcs, and a vertex has
weight its perimeter.

This file ports `GeometricIncidence` from the historical `GeometricCandidate` to
`Embedded.RegionCandidate`.  The O52 charge at either endpoint comes from
`ContiguityGeometry.PieceEquations` (`Estimating/OsinAppendixSectionPieces.lean`).
Lemma 9.1 enters through the endpoint-closed planar edge bound, the graph
content of `(∗)`, as an explicit hypothesis.  With `O52LeastAreaStatement` and no
self-contiguous region, the equations exist at every interior edge of a
least-area diagram (`interior_total_le_of_o52`).
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

open scoped Classical
open GroupApproximation.HullSC

/-- A selected cell-to-cell region, as an edge of `Φ_M`. -/
def InteriorEdge (selected : Finset (RegionCandidate D eps Delta)) :=
  {a : RegionCandidate D eps Delta // a ∈ ofKind selected true}

namespace InteriorEdge

variable {selected : Finset (RegionCandidate D eps Delta)}

noncomputable instance edgeFintype : Fintype (InteriorEdge selected) :=
  inferInstanceAs (Fintype {a : RegionCandidate D eps Delta // a ∈ ofKind selected true})

theorem exists_target (edge : InteriorEdge selected) :
    ∃ i, edge.val.2.target = some i :=
  Option.isSome_iff_exists.mp (Finset.mem_filter.mp edge.property).2

/-- The target cell of an interior edge. -/
noncomputable def target (edge : InteriorEdge selected) : Fin Delta.rCellCount :=
  Classical.choose edge.exists_target

theorem target_eq (edge : InteriorEdge selected) :
    edge.val.2.target = some edge.target :=
  Classical.choose_spec edge.exists_target

/-- A cell is incident to an edge when it is the region's source or target. -/
def Incident (i : Fin Delta.rCellCount) (edge : InteriorEdge selected) : Prop :=
  edge.val.2.source = i ∨ edge.val.2.target = some i

theorem edgesCovered_univ :
    EdgesCovered (Incident (selected := selected)) Finset.univ Finset.univ := by
  intro edge _
  exact ⟨edge.val.2.source, Finset.mem_univ _, Or.inl rfl⟩

theorem hasAtMostTwoEndpoints :
    HasAtMostTwoEndpoints (Incident (selected := selected)) := by
  intro vertices edge
  have hsubset : (vertices.filter fun i => Incident i edge) ⊆
      {edge.val.2.source, edge.target} := by
    intro i hi
    rcases (Finset.mem_filter.mp hi).2 with hs | ht
    · simp [hs]
    · have heq : edge.target = i := Option.some.inj (edge.target_eq.symm.trans ht)
      simp [heq]
  apply le_trans (Finset.card_le_card hsubset)
  have hcard := Finset.card_insert_le edge.val.2.source {edge.target}
  simpa only [Finset.card_singleton] using hcard

/-- **The O52 charge at either endpoint** of an interior edge with its
equations. -/
theorem weight_le_incident {rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (hpieces : ∀ first second word,
      RelWord.IsPublishedPiece D W eps first second word →
        max (first.length : ℝ) (second.length : ℝ) < mu * word.length)
    (hequations : ∀ edge : InteriorEdge selected, edge.val.2.PieceEquations)
    (i : Fin Delta.rCellCount) (edge : InteriorEdge selected)
    (hi : Incident i edge) :
    (edge.val.weight : ℝ) ≤ 2 * mu * ((cell Delta i).word.length : ℝ) := by
  have equations := hequations edge
  rw [weight, Nat.cast_add]
  rcases hi with hs | ht
  · rw [← hs]
    exact edge.val.2.arcLengths_le_two_mu_source equations hsc hpieces
  · have hj : equations.target = i :=
      Option.some.inj (equations.target_eq.symm.trans ht)
    rw [← hj]
    exact edge.val.2.arcLengths_le_two_mu_target equations hsc hpieces

/-- The equations of an interior edge from Osin's least-area O52 clause, when the
region is not self-contiguous. -/
noncomputable def pieceEquations_of_o52 (hO52 : O52LeastAreaStatement.{u, w, v})
    (hlea : Delta.LeastArea) (edge : InteriorEdge selected)
    (hloop : edge.val.2.source ≠ edge.target) : edge.val.2.PieceEquations where
  target := edge.target
  target_eq := edge.target_eq
  whole_ne := hO52 edge.val.2 edge.target edge.target_eq hlea hloop

end InteriorEdge

/-- Subtype indexing keeps the selected interior weights. -/
theorem sum_interior_card_eq_sum_edgeWeight
    (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) :
    (∑ i : Fin Delta.rCellCount, ((boundDarts selected true i).card : ℝ)) =
      ∑ edge : InteriorEdge selected, (edge.val.weight : ℝ) := by
  have hn := sum_interior_card selected hpairwise
  have he : (∑ edge : InteriorEdge selected, edge.val.weight) =
      ∑ a ∈ ofKind selected true, a.weight := Finset.sum_coe_sort _ _
  rw [← he] at hn
  exact_mod_cast hn

/-- **Lemma 9.5's interior budget**, `Σ_inn ≤ 10μΣ`, from the O52 equations at
every interior edge and the endpoint-closed planar edge bound. -/
theorem interior_total_le (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected)
    (hplanar : HasEndpointClosedPlanarEdgeBound
      (InteriorEdge.Incident (selected := selected)))
    (hequations : ∀ edge : InteriorEdge selected, edge.val.2.PieceEquations)
    {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hmu : 0 ≤ mu) :
    (∑ i : Fin Delta.rCellCount, ((boundDarts selected true i).card : ℝ)) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ) := by
  obtain ⟨order⟩ := exists_fiveDeletionOrder_of_endpointClosedPlanarEdgeBound
    InteriorEdge.Incident InteriorEdge.hasAtMostTwoEndpoints hplanar
    Finset.univ Finset.univ InteriorEdge.edgesCovered_univ
    (edgesEndpointClosed_univ _ _)
  have hedge := edgeWeight_sum_le_of_fiveDeletionOrder order
    (2 * mu) (mul_nonneg (by norm_num) hmu)
    (fun i : Fin Delta.rCellCount => ((cell Delta i).word.length : ℝ))
    (fun edge : InteriorEdge selected => (edge.val.weight : ℝ))
    (fun _ => Nat.cast_nonneg _)
    (InteriorEdge.weight_le_incident hcondition.toIsSmallCancellation
      hcondition.publishedPiecesSmall hequations)
  rw [sum_interior_card_eq_sum_edgeWeight selected hpairwise]
  calc
    (∑ edge : InteriorEdge selected, (edge.val.weight : ℝ)) ≤
        5 * (2 * mu) * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ) := by
      simpa using hedge
    _ = _ := by ring

/-- **The interior budget at a least-area diagram**, from `O52LeastAreaStatement`,
no self-contiguous selected region, and the planar edge bound. -/
theorem interior_total_le_of_o52 (hO52 : O52LeastAreaStatement.{u, w, v})
    (hlea : Delta.LeastArea)
    (selected : Finset (RegionCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected)
    (hloops : ∀ edge : InteriorEdge selected, edge.val.2.source ≠ edge.target)
    (hplanar : HasEndpointClosedPlanarEdgeBound
      (InteriorEdge.Incident (selected := selected)))
    {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho) (hmu : 0 ≤ mu) :
    (∑ i : Fin Delta.rCellCount, ((boundDarts selected true i).card : ℝ)) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ) :=
  interior_total_le selected hpairwise hplanar
    (fun edge => InteriorEdge.pieceEquations_of_o52 hO52 hlea edge (hloops edge))
    hcondition hmu

end GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.InteriorEdge.weight_le_incident
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.interior_total_le
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.RegionCandidate.interior_total_le_of_o52
