import GroupApproximation.GGT.VanKampen.Estimating.Deletion
import GroupApproximation.Meta.AxiomGuard

/-!
# Planar deletion with every active endpoint retained

The historical hereditary bound allows a one-vertex state containing an edge
whose other endpoint is absent; it consequently forbids all incidences (#204).
The corrected invariant keeps every endpoint of every active edge. Deleting
a vertex and all incident edges preserves it and supports the same five-owner
and weighted estimates already proved from a deletion order.
-/

namespace GroupApproximation.GGT.VanKampen

universe u v

/-- Every endpoint of every active edge belongs to the active vertex set. -/
def EdgesEndpointClosed {V : Type u} {E : Type v}
    (incident : V → E → Prop) (vertices : Finset V) (edges : Finset E) : Prop :=
  ∀ e ∈ edges, ∀ x, incident x e → x ∈ vertices

/-- The full graph retains all of its endpoints. -/
theorem edgesEndpointClosed_univ {V : Type u} [Fintype V] {E : Type v}
    (incident : V → E → Prop) (edges : Finset E) :
    EdgesEndpointClosed incident Finset.univ edges := by
  intro e he x hx
  exact Finset.mem_univ x

/-- Euler's hereditary inequality on actual subgraph states. Coverage rules
out edges with no endpoint; endpoint closure keeps every actual endpoint. -/
def HasEndpointClosedPlanarEdgeBound
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident] : Prop :=
  ∀ (vertices : Finset V) (edges : Finset E),
    EdgesCovered incident vertices edges → EdgesEndpointClosed incident vertices edges →
      vertices.Nonempty → edges.card ≤ 3 * (vertices.card - 1)

/-- Repeated deletion stays within the endpoint-closed states. -/
theorem exists_fiveDeletionOrder_of_endpointClosedLowDegree
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (hlow : ∀ (vertices : Finset V) (edges : Finset E),
      EdgesCovered incident vertices edges → EdgesEndpointClosed incident vertices edges →
        vertices.Nonempty →
        ∃ x ∈ vertices,
          (incidentEdges incident x edges).card ≤ 5)
    (vertices : Finset V) (edges : Finset E)
    (hcovered : EdgesCovered incident vertices edges)
    (hclosed : EdgesEndpointClosed incident vertices edges) :
    Nonempty (FiveDeletionOrder incident vertices edges) := by
  classical
  induction vertices using Finset.strongInductionOn generalizing edges with
  | _ vertices ih =>
      by_cases hvertices : vertices.Nonempty
      · obtain ⟨x, hx, hdegree⟩ := hlow vertices edges hcovered hclosed hvertices
        have hremaining :
            EdgesCovered incident (remainingVertices x vertices)
              (nonincidentEdges incident x edges) := by
          intro e he
          have he' : e ∈ edges ∧ ¬ incident x e := by
            simpa only [nonincidentEdges, Finset.mem_filter] using he
          have heEdges : e ∈ edges := he'.1
          have hnotIncident : ¬ incident x e := he'.2
          obtain ⟨y, hy, hye⟩ := hcovered e heEdges
          have hyx : y ≠ x := by
            intro hyx
            apply hnotIncident
            rwa [← hyx]
          have hyRemaining : y ∈ remainingVertices x vertices := by
            simpa only [remainingVertices] using Finset.mem_erase.mpr ⟨hyx, hy⟩
          exact ⟨y, hyRemaining, hye⟩
        have hclosedRemaining : EdgesEndpointClosed incident
            (remainingVertices x vertices) (nonincidentEdges incident x edges) := by
          intro e he y hye
          have he' := Finset.mem_filter.mp he
          have hy := hclosed e he'.1 y hye
          have hyx : y ≠ x := by
            intro h
            subst y
            exact he'.2 hye
          exact Finset.mem_erase.mpr ⟨hyx, hy⟩
        have hproper : remainingVertices x vertices ⊂ vertices := by
          simpa only [remainingVertices] using Finset.erase_ssubset hx
        obtain ⟨tail⟩ := ih (remainingVertices x vertices) hproper
          (nonincidentEdges incident x edges) hremaining hclosedRemaining
        exact ⟨FiveDeletionOrder.step x hx hdegree tail⟩
      · have hverticesEmpty : vertices = ∅ := Finset.not_nonempty_iff_eq_empty.mp
          hvertices
        have hedgesEmpty : edges = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hedges
          obtain ⟨e, he⟩ := hedges
          obtain ⟨x, hx, _⟩ := hcovered e he
          rw [hverticesEmpty] at hx
          simp at hx
        rw [hverticesEmpty, hedgesEmpty]
        exact ⟨FiveDeletionOrder.empty⟩

/-- The corrected hereditary Euler inequality supplies a five-deletion
order for every covered state retaining all endpoints. -/
theorem exists_fiveDeletionOrder_of_endpointClosedPlanarEdgeBound
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (htwo : HasAtMostTwoEndpoints incident)
    (hplanar : HasEndpointClosedPlanarEdgeBound incident)
    (vertices : Finset V) (edges : Finset E)
    (hcovered : EdgesCovered incident vertices edges)
    (hclosed : EdgesEndpointClosed incident vertices edges) :
    Nonempty (FiveDeletionOrder incident vertices edges) := by
  apply exists_fiveDeletionOrder_of_endpointClosedLowDegree incident ?_
    vertices edges hcovered hclosed
  intro vertices edges hcovered hclosed hvertices
  have hdegree := sum_incidentEdges_card_le_two_mul incident htwo vertices edges
  have hedge := hplanar vertices edges hcovered hclosed hvertices
  have hcard : 0 < vertices.card := Finset.card_pos.mpr hvertices
  by_contra hnone
  have hlower : 6 * vertices.card ≤
      ∑ x ∈ vertices, (incidentEdges incident x edges).card := by
    calc
      6 * vertices.card = ∑ _x ∈ vertices, 6 := by simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ vertices, (incidentEdges incident x edges).card := by
        apply Finset.sum_le_sum
        intro x hx
        have hnot : ¬ (incidentEdges incident x edges).card ≤ 5 :=
          fun h => hnone ⟨x, hx, h⟩
        omega
  omega

/-- The corrected predicate admits an actual edge with two endpoints. -/
theorem endpointClosedPlanarEdgeBound_singleEdgeModel :
    HasEndpointClosedPlanarEdgeBound (fun (_ : Bool) (_ : Unit) => True) := by
  intro vertices edges _hcovered hclosed _hvertices
  by_cases hempty : edges = ∅
  · simp [hempty]
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hvertices : vertices = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      exact hclosed e he x trivial
    have hedge : edges.card ≤ 1 := by
      have h := Finset.card_le_card (Finset.subset_univ edges)
      simpa using h
    simp only [hvertices, Finset.card_univ, Fintype.card_bool] at *
    omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_fiveDeletionOrder_of_endpointClosedLowDegree
#audit_axioms GroupApproximation.GGT.VanKampen.exists_fiveDeletionOrder_of_endpointClosedPlanarEdgeBound
#audit_closed_axioms GroupApproximation.GGT.VanKampen.endpointClosedPlanarEdgeBound_singleEdgeModel
