import GroupApproximation.GGT.VanKampen.Estimating.GeometricPartition
import GroupApproximation.GGT.VanKampen.Estimating.EndpointClosedDeletion
import GroupApproximation.GGT.VanKampen.Estimating.PieceCore

/-!
# The interior estimate on actual geometric candidates

Every edge is a retained selected cell-to-cell contiguity. Its O52 equations
come from that same witness and reducedness. Endpoint-closed graph deletion
then bounds the actual interior dart count by `10 * mu` times the perimeter.
The planar edge inequality still has to be proved by the geometric producer.
-/

namespace GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate

universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))} {D : RelGenSet G Lambda}
  {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}

open scoped Classical

def InteriorEdge (selected : Finset (GeometricCandidate D eps Delta)) :=
  {a : GeometricCandidate D eps Delta // a ∈ ofKind selected true}

namespace InteriorEdge

variable {selected : Finset (GeometricCandidate D eps Delta)}

noncomputable instance edgeFintype : Fintype (InteriorEdge selected) :=
  inferInstanceAs (Fintype {a : GeometricCandidate D eps Delta // a ∈ ofKind selected true})

theorem exists_target (edge : InteriorEdge selected) :
    ∃ i, edge.val.2.target = some i :=
  Option.isSome_iff_exists.mp (Finset.mem_filter.mp edge.property).2

noncomputable def target (edge : InteriorEdge selected) : Fin Delta.rCellCount :=
  Classical.choose edge.exists_target

theorem target_eq (edge : InteriorEdge selected) :
    edge.val.2.target = some edge.target := Classical.choose_spec edge.exists_target

def Incident (i : Fin Delta.rCellCount) (edge : InteriorEdge selected) : Prop :=
  edge.val.2.source = i ∨ edge.val.2.target = some i

theorem edgesCovered_univ :
    EdgesCovered (Incident (selected := selected)) Finset.univ Finset.univ := by
  intro edge _
  exact ⟨edge.val.2.source, Finset.mem_univ _, Or.inl rfl⟩

theorem hasAtMostTwoEndpoints : HasAtMostTwoEndpoints (Incident (selected := selected)) := by
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

/-- The sum of both retained arcs is charged at either actual endpoint. -/
theorem weight_le_incident (hred : Delta.Reduced) {rho : ℕ} {mu lambda c : ℝ}
    (hcondition : OsinCCondition D W eps mu lambda c rho)
    (i : Fin Delta.rCellCount) (edge : InteriorEdge selected)
    (hi : Incident i edge) :
    (edge.val.weight : ℝ) ≤ 2 * mu * ((cell Delta i).word.length : ℝ) := by
  let equations := edge.val.2.cellPieceEquations_of_reduced hred edge.target_eq
  have hweight : (edge.val.weight : ℝ) =
      (edge.val.2.sourceArc.length : ℝ) +
        ((edge.val.2.cellTargetArc equations.target equations.target_eq).length : ℝ) := by
    rw [weight, Nat.cast_add, Contiguity.cellTargetArc_length]
  rw [hweight]
  rcases hi with hs | ht
  · rw [← hs]
    exact edge.val.2.arcLengths_le_two_mu_source equations
      hcondition.toIsSmallCancellation hcondition.publishedPiecesSmall
  · have hj : equations.target = i := Option.some.inj (equations.target_eq.symm.trans ht)
    rw [← hj]
    exact edge.val.2.arcLengths_le_two_mu_target equations
      hcondition.toIsSmallCancellation hcondition.publishedPiecesSmall

end InteriorEdge

/-- Finite subtype indexing keeps the same selected interior weights. -/
theorem sum_interior_card_eq_sum_edgeWeight
    (selected : Finset (GeometricCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected) :
    (∑ i : Fin Delta.rCellCount, ((boundDarts selected true i).card : ℝ)) =
      ∑ edge : InteriorEdge selected, (edge.val.weight : ℝ) := by
  have hn := sum_interior_card selected hpairwise
  have he : (∑ edge : InteriorEdge selected, edge.val.weight) =
      ∑ a ∈ ofKind selected true, a.weight := Finset.sum_coe_sort _ _
  rw [← he] at hn
  exact_mod_cast hn

/-- O52 and endpoint-closed planar deletion give the exact Osin interior
budget on the corrected geometric selection. -/
theorem interior_total_le (selected : Finset (GeometricCandidate D eps Delta))
    (hpairwise : EstimatingSelection.PairwiseCompatible Compatible selected)
    (hplanar : HasEndpointClosedPlanarEdgeBound
      (InteriorEdge.Incident (selected := selected)))
    (hred : Delta.Reduced) {rho : ℕ} {mu lambda c : ℝ}
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
    (InteriorEdge.weight_le_incident hred hcondition)
  rw [sum_interior_card_eq_sum_edgeWeight selected hpairwise]
  calc
    (∑ edge : InteriorEdge selected, (edge.val.weight : ℝ)) ≤
        5 * (2 * mu) * ∑ i : Fin Delta.rCellCount, ((cell Delta i).word.length : ℝ) := by
      simpa using hedge
    _ = _ := by ring

end GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate

#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.InteriorEdge.weight_le_incident
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.sum_interior_card_eq_sum_edgeWeight
#audit_axioms GroupApproximation.GGT.VanKampen.Embedded.GeometricCandidate.interior_total_le
