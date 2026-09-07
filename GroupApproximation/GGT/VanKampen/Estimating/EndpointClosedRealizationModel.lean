import GroupApproximation.GGT.VanKampen.Estimating.EndpointClosedRealization
import GroupApproximation.GGT.VanKampen.Estimating.UnboundEmptyDisc

/-!
# An edge and an isolated cell satisfy the corrected realization

The one-edge map has a face of degree two, and an isolated vertex has no dart
map at all. These are precisely the cases excluded by the historical
realization in #203. This model constructs every endpoint-closed subgraph
realization for one edge on three vertices, then uses the corrected
component-map theorem to obtain the hereditary bound.
-/

namespace GroupApproximation.GGT.VanKampen.Estimating

/-- The two endpoints of the concrete one-edge map are distinct. -/
theorem emptyDiscMap_loopless : emptyDiscMap.IsLoopless := by
  intro d h
  have hs := (emptyDiscMap.vertexOf_eq_iff _ _).mp h
  have heq : d = emptyDiscMap.alpha d := Equiv.Perm.sameCycle_one.mp hs
  exact emptyDiscMap.alpha_fixedPointFree d heq.symm

/-- The concrete one-edge map has no multiple edges. -/
theorem emptyDiscMap_noMultipleEdges : emptyDiscMap.HasNoMultipleEdges := by
  intro d e h _
  have heq : d = e := Equiv.Perm.sameCycle_one.mp
    ((emptyDiscMap.vertexOf_eq_iff _ _).mp h)
  exact congrArg emptyDiscMap.edgeOf heq

/-- Its unique face has degree two, so the historical face-degree premise
really would reject this simple planar component. -/
theorem emptyDiscMap_faceDegree_two :
    emptyDiscMap.faceDegree (emptyDiscMap.faceOf false) = 2 := by
  classical
  have hsum : (∑ f : emptyDiscMap.Face, emptyDiscMap.faceDegree f) =
      emptyDiscMap.faceDegree (emptyDiscMap.faceOf false) := by
    apply Finset.sum_eq_single
    · intro f _ hne
      exact (hne (emptyDiscMap_face_eq f)).elim
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  have h := emptyDiscMap.sum_faceDegree_eq_two_mul_edgeCount
  rw [hsum, emptyDiscMap_edgeCount] at h
  exact h

/-- A genuine simple planar tree component with a face of degree two. -/
theorem exists_simplePlanarMap_with_twoDartFace :
    ∃ M : CombMap.{0}, M.IsPlanar ∧ M.IsLoopless ∧ M.HasNoMultipleEdges ∧
      M.vertexCount = 2 ∧ M.edgeCount = 1 ∧ ∃ f : M.Face, M.faceDegree f = 2 :=
  ⟨emptyDiscMap, emptyDiscMap_planar, emptyDiscMap_loopless,
    emptyDiscMap_noMultipleEdges, emptyDiscMap_vertexCount,
    emptyDiscMap_edgeCount, emptyDiscMap.faceOf false, emptyDiscMap_faceDegree_two⟩

/-- Incidence of an edge between vertices zero and one; vertex two is isolated. -/
def edgeWithIsolateIncident (x : Fin 3) (_e : Unit) : Prop := x = 0 ∨ x = 1

instance : DecidableRel edgeWithIsolateIncident := fun x _ =>
  inferInstanceAs (Decidable (x = (0 : Fin 3) ∨ x = (1 : Fin 3)))

/-- Every endpoint-closed subgraph of the model has an actual component-map
realization. The edgeless case uses no maps; the other case uses the one-edge
map and omits the isolated vertex. -/
theorem edgeWithIsolate_componentRealizations
    (vertices : Finset (Fin 3)) (edges : Finset Unit)
    (_hcovered : EdgesCovered edgeWithIsolateIncident vertices edges)
    (hclosed : EdgesEndpointClosed edgeWithIsolateIncident vertices edges) :
    ∃ (n : ℕ) (maps : Fin n → CombMap.{0}),
      (∀ i, (maps i).IsPlanar) ∧ (∀ i, (maps i).IsLoopless) ∧
      (∀ i, (maps i).HasNoMultipleEdges) ∧
      edges.card = (∑ i, (maps i).edgeCount) ∧
      (∑ i, (maps i).vertexCount) ≤ vertices.card := by
  classical
  by_cases hempty : edges = ∅
  · subst edges
    exact ⟨0, Fin.elim0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
      (fun i => Fin.elim0 i), by simp, by simp⟩
  · obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hzero : (0 : Fin 3) ∈ vertices := hclosed e he 0 (Or.inl rfl)
    have hone : (1 : Fin 3) ∈ vertices := hclosed e he 1 (Or.inr rfl)
    have hvertices : 2 ≤ vertices.card := by
      have hsub : ({0, 1} : Finset (Fin 3)) ⊆ vertices := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hzero
        · exact hone
      simpa using Finset.card_le_card hsub
    have heq : edges = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      simpa only [Subsingleton.elim x e] using he
    refine ⟨1, (fun _ => emptyDiscMap), (fun _ => emptyDiscMap_planar),
      (fun _ => emptyDiscMap_loopless), (fun _ => emptyDiscMap_noMultipleEdges), ?_, ?_⟩
    · simp [heq, emptyDiscMap_edgeCount]
    · simpa [emptyDiscMap_vertexCount] using hvertices

/-- The corrected hereditary bound is inhabited by an actual nonempty graph
with an isolated vertex, using its component realizations. -/
theorem endpointClosedPlanarEdgeBound_edgeWithIsolate :
    HasEndpointClosedPlanarEdgeBound edgeWithIsolateIncident :=
  hasEndpointClosedPlanarEdgeBound_of_componentMaps edgeWithIsolateIncident
    edgeWithIsolate_componentRealizations

end GroupApproximation.GGT.VanKampen.Estimating

#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.exists_simplePlanarMap_with_twoDartFace
#audit_axioms GroupApproximation.GGT.VanKampen.Estimating.edgeWithIsolate_componentRealizations
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.endpointClosedPlanarEdgeBound_edgeWithIsolate
