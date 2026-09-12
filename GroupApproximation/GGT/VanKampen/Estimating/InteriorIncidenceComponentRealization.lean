import GroupApproximation.GGT.VanKampen.Estimating.EndpointClosedRealization
import GroupApproximation.GGT.VanKampen.Estimating.EndpointClosedAssembly
import GroupApproximation.GGT.VanKampen.Estimating.PhiRealization
import GroupApproximation.GGT.VanKampen.Estimating.HereditaryPlanarRefutation

/-!
# The component realization of the interior incidence graph, named

**This module is a RESHAPE, not a discharge.  It proves nothing new and closes
no admission.**  It gives a name to one geometric obligation that was
previously unnamed, so that the next person does not re-derive the dead ends
recorded below.  The count of open obligations is unchanged.

## What is named

`EndpointClosedRealization.hasEndpointClosedPlanarEdgeBound_of_componentMaps`
produces the corrected Euler invariant from a component realization of an
arbitrary incidence relation.  `InteriorIncidenceComponentRealization` below is
that hypothesis instantiated at the interior incidence graph of a distinguished
family — the only instance the estimating layer needs — and
`hasEndpointClosedPlanarEdgeBound_of_interiorIncidenceComponents` is the
one-line specialisation.

Concretely, the obligation is: decompose each endpoint-closed covered subgraph
of the interior incidence graph into components, embed each component as a
planar loopless simple dart map, and match the counts.  **Nobody has built this
for `Embedded.InteriorEdge.Incident`.**

## Four dead ends, recorded so they are not re-walked

**1.  The existing realization cannot be retargeted.**
`SelectionDichotomy.hasHereditaryPlanarEdgeBound_of_realization` runs on
`InteriorIncidencePlanarRealization`, which is **refuted**
(`HereditaryPlanarRefutation.not_interiorIncidencePlanarRealization`), and the
reason is representability rather than geometry: a dart-based `CombMap` with no
edges has no darts and therefore no vertices (#203), so it cannot realize a
single isolated cell.  That is exactly why the corrected form is *componented*
and may omit isolated vertices.  So the corrected premise is a **different
construction**, not the old one aimed at a better predicate; reusing
`hrealization` would carry the refuted premise into the corrected bound.

**2.  `PhiSimple` is redundant against this hypothesis *shape*, and is
nevertheless on the critical path.**  Read only against the statement above,
Osin's simplicity condition supplies nothing: the component realization already
asserts planarity, looplessness **and** simplicity of the realizing maps, so
there is no `HasNoMultipleEdges` slot for it to fill.

**That is a fact about the shape, and it was originally written here as though
it were a fact about the mathematics.  It is not.**  Counting *producers* rather
than reading the statement gives the opposite emphasis: across the whole
repository `IsLoopless` has exactly one producer and `HasNoMultipleEdges` has
exactly one, both the same hardcoded two-vertex one-edge map
(`EndpointClosedRealizationModel.emptyDiscMap_*`), and every other occurrence of
either predicate is a hypothesis.  There is no parallel-edge merge, contraction
or simplification operation on `CombMap` at all.  Planarity, by contrast, has
some thirty modules behind it and `CombMap.IsRestriction.planar` proved.

So **simplicity is the missing capability**, and the split named below — a
weaker realization omitting simplicity, plus a faithfulness condition
transporting simplicity of the abstract graph to `HasNoMultipleEdges` of the
maps — is not a curiosity to note in passing.  It is the critical path, and
`PhiSimple` is its input.  No such split exists today.

**3.  `PhiSimple` is in any case not available unconditionally.**  It is proved
in exactly two places: inside `Lemma65Statement.lemma65_of_inputs`'s induction,
hence conditional on `Lemma65Inputs` and `Lemma65CutStatement`, neither proved;
and `phiSimple_of_rCellCount_one`, the one-`R`-cell base case.

**4.  The `PhiVertexRotation` route feeds the refuted proposition, so it cannot
be repointed either.**  `PhiRealization.interiorIncidencePlanarRealization_of_vertexRotation`
concludes `InteriorIncidencePlanarRealization`, the proposition refuted in
dead end 1.  Its premise — the unnamed bundle `hrotation`, that every covered
nonempty subgraph admits a planar vertex rotation on its incidence darts with
`vertexCount = vertices.card` — is therefore **false**, by composition with
`not_interiorIncidencePlanarRealization`.  The failure is at the same point:
take `edges = ∅` and one vertex, and `PhiVertexRotation` is asked for a
`phiMap` over an empty dart type whose `vertexCount` is `1`, contradicting
`CombMap.vertexCount_eq_zero_of_edgeCount_eq_zero`.  So `phiMap`, `phiAlpha`
and their edge-count lemmas remain reusable, but the *rotation hypothesis* as
stated is not a route to anything; a corrected version must ask for
`vertexCount ≤ vertices.card` componentwise, which is what the obligation above
does.  **This one is checked, not asserted:** `not_phiVertexRotationBundle`
below proves it, so dead end 4 stands on the same footing as dead end 1 rather
than on a header claim.

## The bundle comparison, for the record

`Lemma65aConclusion` is `PhiSimple ∧ ExteriorMergeAvailable`;
`EndpointClosedEstimatingGraphData` is the corrected Euler bound together with
the same `ExteriorMergeAvailable`.  As definitions the two remaining clauses are
**incomparable**, with a counterexample each way: two parallel edges on two
vertices satisfy `2 ≤ 3 * (2 - 1)` while failing simplicity, so the bound does
not imply `PhiSimple`; and simplicity carries no cardinality content at all —
`K₇` is simple with `21 > 3 * 6` — so **without planarity the implication fails
in that direction too**.  Anyone deriving one from the other without the ambient
geometry is proving something false.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u w v z

/-- **The component realization of the interior incidence graph.**  The single
geometric obligation behind the corrected Euler invariant for a distinguished
family: every endpoint-closed covered subgraph is realized by finitely many
planar, loopless, simple dart maps whose edge counts sum to the subgraph's and
whose vertex counts do not exceed it.

This is a *name for an obligation*, not a theorem.  Nothing in this repository
produces it, and this module does not claim otherwise. -/
def InteriorIncidenceComponentRealization
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Embedded.Candidate D eps Delta)) : Prop :=
  ∀ (vertices : Finset (Fin Delta.rCellCount))
    (edges : Finset (Embedded.InteriorEdge selected)),
    EdgesCovered (Embedded.InteriorEdge.Incident (selected := selected))
        vertices edges →
      EdgesEndpointClosed (Embedded.InteriorEdge.Incident (selected := selected))
        vertices edges →
      ∃ (n : ℕ) (maps : Fin n → CombMap.{z}),
        (∀ i, (maps i).IsPlanar) ∧ (∀ i, (maps i).IsLoopless) ∧
        (∀ i, (maps i).HasNoMultipleEdges) ∧
        edges.card = (∑ i, (maps i).edgeCount) ∧
        (∑ i, (maps i).vertexCount) ≤ vertices.card

/-- **The corrected Euler invariant, from the named obligation.**  One
application of `hasEndpointClosedPlanarEdgeBound_of_componentMaps`.

This discharges nothing: it renames `hrealization` at the one incidence
relation the estimating layer uses, so that the obligation can be cited and
tracked rather than re-derived. -/
theorem hasEndpointClosedPlanarEdgeBound_of_interiorIncidenceComponents
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W}
    (selected : Finset (Embedded.Candidate D eps Delta))
    (hrealization : InteriorIncidenceComponentRealization.{u, w, v, z} selected) :
    HasEndpointClosedPlanarEdgeBound
      (Embedded.InteriorEdge.Incident (selected := selected)) :=
  hasEndpointClosedPlanarEdgeBound_of_componentMaps _ hrealization

/-- **Dead end 4, checked rather than asserted.**  The premise of
`Embedded.interiorIncidencePlanarRealization_of_vertexRotation` is false.

That theorem concludes `InteriorIncidencePlanarRealization`, which
`not_interiorIncidencePlanarRealization` refutes, so its unnamed hypothesis
bundle cannot hold.  Stated here at universe `0` because the refutation is.

This is a refutation, not a discharge: it closes no obligation.  It converts a
recorded dead end into a checked one, so that the `PhiVertexRotation` route is
known dead by the build rather than by this module's prose.  `phiMap`,
`phiAlpha` and the edge-count lemmas are untouched and remain reusable — only
the rotation hypothesis is dead. -/
theorem not_phiVertexRotationBundle :
    ¬ (∀ {G : Type} [Group G] {Lambda : Type}
      {D : GGT.RelGenSet G Lambda}
      {W : Set (List (GGT.RelLetter G Lambda))}
      {eps : ℕ} {Delta : DiscDiagram.{0, 0, 0} W}
      (selected : Finset (Embedded.Candidate D eps Delta))
      (vertices : Finset (Fin Delta.rCellCount))
      (edges : Finset (Embedded.InteriorEdge selected)),
      EdgesCovered (Embedded.InteriorEdge.Incident (selected := selected))
          vertices edges →
        vertices.Nonempty →
        Embedded.PhiVertexRotation {e : Embedded.InteriorEdge selected // e ∈ edges}
          vertices.card) := by
  intro hrotation
  exact not_interiorIncidencePlanarRealization
    (Embedded.interiorIncidencePlanarRealization_of_vertexRotation hrotation)

/-- **Model test: the obligation is satisfiable.**  At the empty distinguished
family `InteriorEdge` is an empty type, so every covered endpoint-closed
subgraph is edgeless and the empty family of maps realizes it.

**This model is DEGENERATE and the docstring says so on purpose.**  What it
establishes: `InteriorIncidenceComponentRealization` is not refuted — it has a
model, so no consumer rests on a false hypothesis, and the standing
model-test requirement is met rather than skipped.  What it does **not**
establish: anything about non-vacuity in the regime that matters.  It never
builds a single `CombMap`, never uses `EdgesEndpointClosed`, and never touches
planarity, so it cannot distinguish this obligation from one that is true only
because it is empty.

**The non-degenerate model is open**: an instantiation at a `selected` with at
least one interior edge, where a real map must be produced and counted.  The
generic hypothesis shape does have such a model —
`EndpointClosedRealizationModel.edgeWithIsolate_componentRealizations`, at one
real edge and one real isolated cell — but at a different incidence relation,
so it is a template rather than a substitute. -/
theorem interiorIncidenceComponentRealization_empty
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {eps : ℕ}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, v} W} :
    InteriorIncidenceComponentRealization.{u, w, v, z}
      (∅ : Finset (Embedded.Candidate D eps Delta)) := by
  classical
  intro vertices edges _hcovered _hclosed
  have hempty : edges = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e _
    exact absurd e.2.1 (Finset.notMem_empty _)
  subst hempty
  exact ⟨0, Fin.elim0, (fun i => Fin.elim0 i), (fun i => Fin.elim0 i),
    (fun i => Fin.elim0 i), by simp, by simp⟩

/-! Checked on every build, and checked BY NAME by the landing gate.  `#print
axioms` would report the same closure passively; `#audit_axioms` refuses the
build if this declaration ever acquires a non-classical dependency, and it is
the form the landing gate can look for.  It certifies the *closure* only: this
theorem is conditional on `hrealization`, which nothing produces. -/

#audit_axioms GroupApproximation.GGT.VanKampen.hasEndpointClosedPlanarEdgeBound_of_interiorIncidenceComponents
#audit_closed_axioms GroupApproximation.GGT.VanKampen.not_phiVertexRotationBundle
#audit_axioms GroupApproximation.GGT.VanKampen.interiorIncidenceComponentRealization_empty

end VanKampen
end GGT
end GroupApproximation
