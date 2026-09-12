import GroupApproximation.GGT.VanKampen.CombMap
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The underlying simple graph of a combinatorial map

Forgetting loops and identifying parallel edges preserves vertex reachability.
Every resulting simple edge comes from an actual map edge, so the connected
graph bound gives `V ≤ E + 1` without any planarity assumption on the map.
-/

namespace GroupApproximation.GGT.VanKampen.CombMap

universe u
variable (M : CombMap.{u})

/-- The simple graph on the actual vertex quotient, forgetting loops and
identifying parallel edges. -/
def underlyingGraph : SimpleGraph M.Vertex where
  Adj v w := v ≠ w ∧ ∃ d : M.Dart,
    M.vertexOf d = v ∧ M.vertexOf (M.alpha d) = w
  symm := ⟨by
    rintro v w ⟨hne, d, hd, ha⟩
    exact ⟨hne.symm, M.alpha d, ha, by rw [M.alpha_involutive]; exact hd⟩⟩
  loopless := ⟨by rintro v ⟨hne, _⟩; exact hne rfl⟩

theorem underlyingGraph_reachable_alpha (d : M.Dart) :
    M.underlyingGraph.Reachable (M.vertexOf d) (M.vertexOf (M.alpha d)) := by
  by_cases h : M.vertexOf d = M.vertexOf (M.alpha d)
  · rw [h]
  · exact SimpleGraph.Adj.reachable (show M.underlyingGraph.Adj _ _ from
      ⟨h, d, rfl, rfl⟩)

/-- Dart paths descend to paths in the actual underlying graph. -/
theorem underlyingGraph_reachable {d e : M.Dart}
    (h : Relation.EqvGen M.Adjacent d e) :
    M.underlyingGraph.Reachable (M.vertexOf d) (M.vertexOf e) := by
  induction h with
  | rel d e h =>
      rcases h with rfl | rfl
      · exact M.underlyingGraph_reachable_alpha d
      · rw [M.vertexOf_sigma]
  | refl d => exact .rfl
  | symm d e _ ih => exact ih.symm
  | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem underlyingGraph_preconnected (hM : M.IsConnected) :
    M.underlyingGraph.Preconnected := by
  intro v w
  refine Quotient.inductionOn₂ v w ?_
  intro d e
  exact M.underlyingGraph_reachable (hM d e)

/-- The unordered pair of endpoints of a map edge is independent of its
orientation, even for a loop. -/
def edgeEndpoints : M.Edge → Sym2 M.Vertex :=
  Quotient.lift (fun d => s(M.vertexOf d, M.vertexOf (M.alpha d))) (by
    intro d e h
    rcases h with rfl | rfl
    · rfl
    · rw [M.alpha_involutive]
      exact Sym2.eq_swap)

theorem exists_edgeEndpoints (e : M.underlyingGraph.edgeSet) :
    ∃ a : M.Edge, M.edgeEndpoints a = e.1 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf v w =>
      obtain ⟨_, d, hd, ha⟩ := (SimpleGraph.mem_edgeSet M.underlyingGraph).mp he
      refine ⟨M.edgeOf d, ?_⟩
      change s(M.vertexOf d, M.vertexOf (M.alpha d)) = s(v, w)
      rw [hd, ha]

/-- The simple graph has no more edges than the map from which it was
constructed; loops and parallel edges need no exclusion hypothesis. -/
theorem underlyingGraph_edge_card_le :
    Nat.card M.underlyingGraph.edgeSet ≤ M.edgeCount := by
  classical
  let f : M.underlyingGraph.edgeSet → M.Edge :=
    fun e => Classical.choose (M.exists_edgeEndpoints e)
  have hf (e : M.underlyingGraph.edgeSet) : M.edgeEndpoints (f e) = e.1 :=
    Classical.choose_spec (M.exists_edgeEndpoints e)
  apply Nat.card_le_card_of_injective f
  intro e e' h
  apply Subtype.ext
  exact (hf e).symm.trans ((congrArg M.edgeEndpoints h).trans (hf e'))

/-- Every connected combinatorial map satisfies the graph bound, including
the empty map. No Euler or planarity hypothesis is used. -/
theorem vertexCount_le_edgeCount_add_one (hM : M.IsConnected) :
    M.vertexCount ≤ M.edgeCount + 1 := by
  cases isEmpty_or_nonempty M.Vertex with
  | inl h =>
      letI := h
      simp [vertexCount]
  | inr h =>
      have hc : M.underlyingGraph.Connected :=
        { preconnected := M.underlyingGraph_preconnected hM, nonempty := h }
      exact hc.card_vert_le_card_edgeSet_add_one.trans
        (Nat.add_le_add_right M.underlyingGraph_edge_card_le 1)

/-- If every edge has equal endpoints, connectedness puts all darts at one
vertex. This also allows the empty map. -/
theorem vertexCount_le_one_of_same_endpoints (hM : M.IsConnected)
    (hedge : ∀ d : M.Dart, M.vertexOf d = M.vertexOf (M.alpha d)) :
    M.vertexCount ≤ 1 := by
  have hpath {d e : M.Dart} (h : Relation.EqvGen M.Adjacent d e) :
      M.vertexOf d = M.vertexOf e := by
    induction h with
    | rel d e h =>
        rcases h with rfl | rfl
        · exact hedge d
        · exact (M.vertexOf_sigma d).symm
    | refl d => rfl
    | symm d e _ ih => exact ih.symm
    | trans d e f _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  letI : Subsingleton M.Vertex := ⟨fun v w => Quotient.inductionOn₂ v w
    (fun d e => hpath (hM d e))⟩
  simpa only [vertexCount, Nat.card_eq_fintype_card] using
    (Fintype.card_le_one_iff_subsingleton.mpr (inferInstance : Subsingleton M.Vertex))

end GroupApproximation.GGT.VanKampen.CombMap

#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.underlyingGraph_edge_card_le
#audit_axioms GroupApproximation.GGT.VanKampen.CombMap.vertexCount_le_edgeCount_add_one
