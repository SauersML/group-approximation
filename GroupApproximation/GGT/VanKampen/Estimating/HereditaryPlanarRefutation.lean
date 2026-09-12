import GroupApproximation.GGT.VanKampen.Estimating.SelectionDichotomy
import GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample

/-!
# Two obstructions in the historical estimating-graph interfaces

`EdgesCovered` only requires one endpoint of each edge. Applying the proposed
hereditary Euler bound to one vertex and one incident edge therefore shows
that it forbids every incidence (#204). Independently, a dart-based `CombMap`
cannot realize one isolated vertex and no edges (#203).
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

/-- The historical hereditary bound forbids any single incidence. -/
theorem not_incident_of_hereditaryPlanarEdgeBound
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (h : HasHereditaryPlanarEdgeBound incident) (x : V) (e : E) :
    ¬ incident x e := by
  intro hxe
  have hcovered : EdgesCovered incident {x} {e} := by
    intro f hf
    have heq : f = e := Finset.mem_singleton.mp hf
    subst f
    exact ⟨x, Finset.mem_singleton_self x, hxe⟩
  have hbound := h {x} {e} hcovered (Finset.singleton_nonempty x)
  simp at hbound

/-- Exact classification of the defective historical predicate. -/
theorem hereditaryPlanarEdgeBound_iff_no_incidence
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident] :
    HasHereditaryPlanarEdgeBound incident ↔ ∀ x e, ¬ incident x e := by
  constructor
  · exact fun h => not_incident_of_hereditaryPlanarEdgeBound incident h
  · intro h vertices edges hcovered _
    have hempty : edges = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
      intro e he
      obtain ⟨x, _hx, hxe⟩ := hcovered e he
      exact h x e hxe)
    simp [hempty]

/-- The actual historical graph certificate admits no selected interior edge. -/
theorem EstimatingGraphData.no_interiorEdge
    {G : Type u} [Group G] {Lambda : Type w}
    {D : RelGenSet G Lambda} {W : Set (List (RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {scaffold : EstimatingScaffold D eps Delta}
    (graph : EstimatingGraphData D eps Delta scaffold)
    (edge : Embedded.InteriorEdge scaffold.selected.family) : False := by
  classical
  apply not_incident_of_hereditaryPlanarEdgeBound
    (Embedded.InteriorEdge.Incident (selected := scaffold.selected.family))
    graph.planarEdgeBound edge.candidate.contiguity.source edge
  exact Or.inl rfl

/-- A map with no edge has no dart and hence no vertex orbit. -/
theorem CombMap.vertexCount_eq_zero_of_edgeCount_eq_zero
    (M : CombMap.{v}) (h : M.edgeCount = 0) : M.vertexCount = 0 := by
  classical
  haveI : IsEmpty M.Edge := Fintype.card_eq_zero_iff.mp (by
    simpa only [CombMap.edgeCount, Nat.card_eq_fintype_card] using h)
  haveI : IsEmpty M.Dart := ⟨fun d => isEmptyElim (M.edgeOf d)⟩
  simp [CombMap.vertexCount]

/-- The historical realization cannot represent even a single isolated cell.
The concrete positive-cell source diagram is already constructed in Lean. -/
theorem not_interiorIncidencePlanarRealization :
    ¬ InteriorIncidencePlanarRealization.{0, 0, 0} := by
  classical
  intro h
  obtain ⟨Delta, _hred, hcount, _hboundary, _⟩ :=
    Estimating.UnboundSmallMuCounterexample.exists_counterexample
  let x : Fin Delta.rCellCount := ⟨0, by omega⟩
  let selected : Finset (Embedded.Candidate
    Estimating.UnboundSmallMuCounterexample.D 0 Delta) := ∅
  have hcovered : EdgesCovered
      (Embedded.InteriorEdge.Incident (selected := selected)) {x} ∅ := by
    intro e he
    simp at he
  obtain ⟨M, _hplanar, _hfaces, hvertex, hedge⟩ :=
    h selected {x} ∅ hcovered (Finset.singleton_nonempty x)
  have hedge0 : M.edgeCount = 0 := by simpa only [Finset.card_empty] using hedge
  have hvertex0 := M.vertexCount_eq_zero_of_edgeCount_eq_zero hedge0
  simp only [Finset.card_singleton] at hvertex
  omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.hereditaryPlanarEdgeBound_iff_no_incidence
#audit_axioms GroupApproximation.GGT.VanKampen.EstimatingGraphData.no_interiorEdge
#audit_closed_axioms GroupApproximation.GGT.VanKampen.not_interiorIncidencePlanarRealization
