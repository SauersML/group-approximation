import GroupApproximation.GGT.VanKampen.CombMapSimpleEuler
import GroupApproximation.GGT.VanKampen.Estimating.EndpointClosedDeletion

/-!
# Component realization for the corrected estimating graph

Represent only the components containing edges by simple planar dart maps.
The sum of their vertex counts may be smaller than the number of active cells:
isolated cells need no fictitious dart-map realization. A zero-component
realization covers the edgeless state. The Euler theorem also admits tree
components, including the one-edge case.

These are reductions from actual component maps, not a claim that the maps
of a distinguished contiguity family have already been constructed.
-/

namespace GroupApproximation.GGT.VanKampen

universe u v z

/-- Simple planar components give the required bound even when some vertices
are isolated, or when there are no edges at all. -/
theorem edgeBound_of_simplePlanarComponents
    {n totalVertices totalEdges : ℕ} (maps : Fin n → CombMap.{z})
    (hplanar : ∀ i, (maps i).IsPlanar)
    (hloop : ∀ i, (maps i).IsLoopless)
    (hmulti : ∀ i, (maps i).HasNoMultipleEdges)
    (hedges : totalEdges = ∑ i, (maps i).edgeCount)
    (hvertices : (∑ i, (maps i).vertexCount) ≤ totalVertices) :
    totalEdges ≤ 3 * (totalVertices - 1) := by
  by_cases hn : n = 0
  · subst n
    have he : totalEdges = 0 := by simpa using hedges
    simp [he]
  · exact edgeBound_of_components (Nat.pos_of_ne_zero hn)
      (fun i => (maps i).vertexCount) (fun i => (maps i).edgeCount)
      (fun i => (maps i).vertexCount_pos_of_planar (hplanar i)) hedges hvertices
      (fun i => (maps i).edgeCount_le_three_mul_vertex_sub_one_of_simple
        (hplanar i) (hloop i) (hmulti i))

/-- Construct the corrected hereditary invariant from simple planar
realizations of actual endpoint-closed subgraphs. The realization is allowed
to omit isolated vertices and has no face-degree input. -/
theorem hasEndpointClosedPlanarEdgeBound_of_componentMaps
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (hrealization : ∀ (vertices : Finset V) (edges : Finset E),
      EdgesCovered incident vertices edges → EdgesEndpointClosed incident vertices edges →
        ∃ (n : ℕ) (maps : Fin n → CombMap.{z}),
          (∀ i, (maps i).IsPlanar) ∧ (∀ i, (maps i).IsLoopless) ∧
          (∀ i, (maps i).HasNoMultipleEdges) ∧
          edges.card = (∑ i, (maps i).edgeCount) ∧
          (∑ i, (maps i).vertexCount) ≤ vertices.card) :
    HasEndpointClosedPlanarEdgeBound incident := by
  intro vertices edges hcovered hclosed _hvertices
  obtain ⟨n, maps, hplanar, hloop, hmulti, hedge, hvertex⟩ :=
    hrealization vertices edges hcovered hclosed
  exact edgeBound_of_simplePlanarComponents maps hplanar hloop hmulti hedge hvertex

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.edgeBound_of_simplePlanarComponents
#audit_axioms GroupApproximation.GGT.VanKampen.hasEndpointClosedPlanarEdgeBound_of_componentMaps
