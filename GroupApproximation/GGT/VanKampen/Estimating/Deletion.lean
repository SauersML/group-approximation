import GroupApproximation.GGT.VanKampen.CombMap
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Deletion orders for estimating maps

This file proves the inductive part of Osin's Appendix Lemma `Eul`.  A
deletion order removes one vertex together with all active incident edges.
If at most five edges are removed at every step, then the weighted sum of
edges is at most five times the incidence constant times the weighted sum of
vertices.

For a `CombMap`, incidence is defined through darts.  The last theorem turns
the low-degree conclusion for every remaining finite incidence state into a
five-deletion order.  A planar deletion construction can use this theorem
after applying the one-step Euler estimate to each remaining component.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

universe u v

/-! ## Finite deletion orders -/

/-- An edge set is covered by a vertex set when every active edge is incident
to at least one active vertex. -/
def EdgesCovered
    {V : Type u} {E : Type v}
    (incident : V → E → Prop) (vertices : Finset V) (edges : Finset E) :
    Prop :=
  ∀ e ∈ edges, ∃ x ∈ vertices, incident x e

/-- The active edges incident to a selected vertex. -/
def incidentEdges
    {V : Type u} {E : Type v} [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (x : V) (edges : Finset E) : Finset E := by
  exact edges.filter fun e => incident x e

/-- The active edges retained after deleting a selected vertex. -/
def nonincidentEdges
    {V : Type u} {E : Type v} [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (x : V) (edges : Finset E) : Finset E := by
  exact edges.filter fun e => ¬ incident x e

/-- The vertices retained after deleting a selected vertex. -/
def remainingVertices
    {V : Type u} [DecidableEq V] (x : V) (vertices : Finset V) : Finset V := by
  exact vertices.erase x

/-- A five-deletion order removes a vertex and all currently active edges
incident to it.  Its terminal state has no vertices and no edges. -/
inductive FiveDeletionOrder
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident] :
    Finset V → Finset E → Prop where
  | empty : FiveDeletionOrder incident ∅ ∅
  | step {vertices : Finset V} {edges : Finset E} (x : V)
      (hx : x ∈ vertices)
      (hdegree : (incidentEdges incident x edges).card ≤ 5)
      (tail : FiveDeletionOrder incident (remainingVertices x vertices)
        (nonincidentEdges incident x edges)) :
      FiveDeletionOrder incident vertices edges

/-! ## Five-owner orientations -/

/-- A five-owner orientation assigns every active edge to one incident active
vertex, with at most five edges assigned to any active vertex.  This is the
orientation conclusion of Osin's Appendix Lemma `Eul`. -/
structure FiveOwnerOrientation
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (vertices : Finset V) (edges : Finset E) where
  owner : E → V
  owner_mem : ∀ e ∈ edges, owner e ∈ vertices ∧ incident (owner e) e
  owner_card : ∀ x ∈ vertices,
    (edges.filter (fun e => owner e = x)).card ≤ 5

namespace FiveDeletionOrder

/-- The deletion order recursively assigns each removed edge to the vertex
removed at that step. -/
theorem toOwnerOrientation
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    {vertices : Finset V} {edges : Finset E}
    (order : FiveDeletionOrder incident vertices edges)
    [Nonempty V] :
    Nonempty (FiveOwnerOrientation incident vertices edges) := by
  induction order with
  | empty =>
      let x₀ : V := Classical.choice (inferInstance : Nonempty V)
      refine ⟨{
        owner := fun _ => x₀
        owner_mem := ?_
        owner_card := ?_ }⟩
      · intro e he
        simp at he
      · intro x hx
        simp at hx
  | @step vertices edges x hx hdegree tail ih =>
      obtain ⟨tailOrientation⟩ := ih
      let owner : E → V := fun e =>
        if incident x e then x else tailOrientation.owner e
      refine ⟨{
        owner := owner
        owner_mem := ?_
        owner_card := ?_ }⟩
      · intro e he
        by_cases hxe : incident x e
        · simp only [owner, hxe, ↓reduceIte]
          exact ⟨hx, trivial⟩
        · have hnonincident : e ∈ nonincidentEdges incident x edges := by
            simp only [nonincidentEdges, Finset.mem_filter, he, true_and]
            exact hxe
          have htail := tailOrientation.owner_mem e hnonincident
          have hnotx : tailOrientation.owner e ≠ x := by
            intro heq
            have hmem := htail.1
            rw [heq] at hmem
            exact (Finset.mem_erase.mp hmem).1 rfl
          rw [show owner e = tailOrientation.owner e by
            simp only [owner, hxe, ↓reduceIte]]
          exact ⟨Finset.mem_of_mem_erase htail.1, htail.2⟩
      · intro y hy
        by_cases hyx : y = x
        · subst y
          have hfilter :
              edges.filter (fun e => owner e = x) =
                incidentEdges incident x edges := by
            ext e
            simp only [Finset.mem_filter, incidentEdges]
            change (e ∈ edges ∧ owner e = x) ↔
              (e ∈ edges ∧ incident x e)
            by_cases hxe : incident x e
            · constructor
              · intro h
                exact ⟨h.1, hxe⟩
              · intro h
                have hmem : e ∈ edges ∧ incident x e := h
                simp only [owner, hxe, ↓reduceIte]
                exact ⟨hmem.1, trivial⟩
            · constructor
              · intro h
                have hnonincident : e ∈ nonincidentEdges incident x edges :=
                  Finset.mem_filter.mpr ⟨h.1, hxe⟩
                have howner := tailOrientation.owner_mem e hnonincident
                have hne : tailOrientation.owner e ≠ x := by
                  intro heq
                  have hmem := howner.1
                  rw [heq] at hmem
                  exact (Finset.mem_erase.mp hmem).1 rfl
                have hownerEq : tailOrientation.owner e = x := by
                  simpa only [owner, hxe, ↓reduceIte] using h.2
                exact (hne hownerEq).elim
              · intro h
                exact (hxe h.2).elim
          rw [hfilter]
          exact hdegree
        · have hyRemaining : y ∈ remainingVertices x vertices := by
            exact Finset.mem_erase.mpr ⟨hyx, hy⟩
          have htail := tailOrientation.owner_card y hyRemaining
          have hfilter :
              edges.filter (fun e => owner e = y) =
                (nonincidentEdges incident x edges).filter
                  (fun e => tailOrientation.owner e = y) := by
            ext e
            simp only [Finset.mem_filter, nonincidentEdges]
            change (e ∈ edges ∧ owner e = y) ↔
              ((e ∈ edges ∧ ¬ incident x e) ∧
                tailOrientation.owner e = y)
            by_cases he : e ∈ edges
            · by_cases hxe : incident x e
              · have hxyeq : x ≠ y := by
                  intro hxy
                  exact hyx hxy.symm
                simp [owner, nonincidentEdges, he, hxe, hxyeq]
              · simp [owner, nonincidentEdges, he, hxe]
            · simp only [he, false_and]
          rw [hfilter]
          exact htail

end FiveDeletionOrder

/-! ## Model checks -/

/-- The empty incidence state has a five-owner orientation whenever its
ambient vertex type is inhabited. -/
theorem fiveOwnerOrientation_emptyModel
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident] [Nonempty V] :
    Nonempty (FiveOwnerOrientation incident (∅ : Finset V) (∅ : Finset E)) := by
  exact FiveDeletionOrder.toOwnerOrientation incident FiveDeletionOrder.empty

/-- The empty incidence state is the base model for a five-deletion order. -/
theorem fiveDeletionOrder_emptyModel
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident] :
    FiveDeletionOrder incident ∅ ∅ :=
  FiveDeletionOrder.empty

/-- If every nonempty covered state has a vertex of active degree at most
five, repeated deletion gives a five-deletion order.  This is the finite
induction in Osin's Appendix Lemma `Eul`. -/
theorem exists_fiveDeletionOrder_of_lowDegree
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (hlow : ∀ (vertices : Finset V) (edges : Finset E),
      EdgesCovered incident vertices edges → vertices.Nonempty →
        ∃ x ∈ vertices,
          (incidentEdges incident x edges).card ≤ 5)
    (vertices : Finset V) (edges : Finset E)
    (hcovered : EdgesCovered incident vertices edges) :
    Nonempty (FiveDeletionOrder incident vertices edges) := by
  classical
  induction vertices using Finset.strongInductionOn generalizing edges with
  | _ vertices ih =>
      by_cases hvertices : vertices.Nonempty
      · obtain ⟨x, hx, hdegree⟩ := hlow vertices edges hcovered hvertices
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
        have hproper : remainingVertices x vertices ⊂ vertices := by
          simpa only [remainingVertices] using Finset.erase_ssubset hx
        obtain ⟨tail⟩ := ih (remainingVertices x vertices) hproper
          (nonincidentEdges incident x edges) hremaining
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

/-! ## The hereditary Euler input -/

/-- Every active edge has at most two distinct incident vertices. -/
def HasAtMostTwoEndpoints
    {V : Type u} {E : Type v} [DecidableEq V]
    (incident : V → E → Prop) [DecidableRel incident] : Prop :=
  ∀ (vertices : Finset V) (edge : E),
    (vertices.filter fun x => incident x edge).card ≤ 2

/-- The empty-edge one-vertex incidence relation has at most two endpoints
per edge. -/
theorem atMostTwoEndpoints_oneVertexNoEdgesModel
    (incident : PUnit → PEmpty → Prop) [DecidableRel incident] :
    HasAtMostTwoEndpoints incident := by
  intro _ edge
  exact edge.elim

/-- Double-counting vertex-edge incidences bounds the active degree sum by
twice the number of active edges. -/
theorem sum_incidentEdges_card_le_two_mul
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (htwo : HasAtMostTwoEndpoints incident)
    (vertices : Finset V) (edges : Finset E) :
    (∑ x ∈ vertices, (incidentEdges incident x edges).card) ≤
      2 * edges.card := by
  classical
  have hreindex :
      (∑ x ∈ vertices, (incidentEdges incident x edges).card) =
        ∑ edge ∈ edges, (vertices.filter fun x => incident x edge).card := by
    simp_rw [incidentEdges, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hreindex]
  calc
    (∑ edge ∈ edges, (vertices.filter fun x => incident x edge).card) ≤
        ∑ _edge ∈ edges, 2 := by
      exact Finset.sum_le_sum fun edge _ => htwo vertices edge
    _ = 2 * edges.card := by simp [Nat.mul_comm]

/-- The edge inequality for every nonempty covered deletion state.  For the
simple planar estimating graph this is Euler's inequality
`|E| ≤ 3 * (|V| - 1)`, applied componentwise when the state is disconnected. -/
def HasHereditaryPlanarEdgeBound
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident] : Prop :=
  ∀ (vertices : Finset V) (edges : Finset E),
    EdgesCovered incident vertices edges → vertices.Nonempty →
      edges.card ≤ 3 * (vertices.card - 1)

/-- The one-vertex graph with no edges satisfies the hereditary planar edge
bound at equality. -/
theorem hereditaryPlanarEdgeBound_oneVertexNoEdgesModel
    (incident : PUnit → PEmpty → Prop) [DecidableRel incident] :
    HasHereditaryPlanarEdgeBound incident := by
  intro vertices edges _ hvertices
  have hedges : edges = ∅ := Subsingleton.elim _ _
  rw [hedges]
  simp

/-- Every nonempty covered deletion state has average active degree below
six.  For a simple planar graph this is the hereditary Euler inequality
obtained by deleting vertices and treating connected components separately. -/
def HasHereditaryAverageDegreeLtSix
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident] : Prop :=
  ∀ (vertices : Finset V) (edges : Finset E),
    EdgesCovered incident vertices edges → vertices.Nonempty →
      (∑ x ∈ vertices, (incidentEdges incident x edges).card) <
        6 * vertices.card

/-- The hereditary average-degree condition holds for the one-vertex graph
with no edges, so it does not obtain its conclusion from an empty vertex
set. -/
theorem hereditaryAverageDegree_oneVertexNoEdgesModel
    (incident : PUnit → PEmpty → Prop) [DecidableRel incident] :
    HasHereditaryAverageDegreeLtSix incident := by
  intro vertices edges _ hvertices
  have hedges : edges = ∅ := Subsingleton.elim _ _
  rw [hedges]
  have hcardPos : 0 < vertices.card := Finset.card_pos.mpr hvertices
  simp only [incidentEdges, Finset.filter_empty, Finset.card_empty,
    Finset.sum_const_zero]
  omega

/-- Euler's hereditary edge bound and the two-endpoint property imply the
hereditary average-degree estimate used by the deletion induction. -/
theorem hereditaryAverageDegree_of_planarEdgeBound
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (htwo : HasAtMostTwoEndpoints incident)
    (hplanar : HasHereditaryPlanarEdgeBound incident) :
    HasHereditaryAverageDegreeLtSix incident := by
  intro vertices edges hcovered hvertices
  have hdegree := sum_incidentEdges_card_le_two_mul incident htwo vertices edges
  have hedge := hplanar vertices edges hcovered hvertices
  have hcard : 0 < vertices.card := Finset.card_pos.mpr hvertices
  omega

/-- Componentwise edge bounds combine to the same bound for a disconnected
deletion state.  Isolated active vertices may be omitted from the component
sum because only `sum vertexCount ≤ totalVertices` is required. -/
theorem edgeBound_of_components
    {componentCount totalVertices totalEdges : ℕ}
    (hcomponents : 0 < componentCount)
    (vertexCount edgeCount : Fin componentCount → ℕ)
    (hvertexPos : ∀ i, 0 < vertexCount i)
    (hedges : totalEdges = ∑ i : Fin componentCount, edgeCount i)
    (hvertices : (∑ i : Fin componentCount, vertexCount i) ≤ totalVertices)
    (hcomponent : ∀ i, edgeCount i ≤ 3 * (vertexCount i - 1)) :
    totalEdges ≤ 3 * (totalVertices - 1) := by
  have hlocal : ∀ i : Fin componentCount,
      edgeCount i + 3 ≤ 3 * vertexCount i := by
    intro i
    have hpos := hvertexPos i
    have hbound := hcomponent i
    omega
  have hsum :
      (∑ i : Fin componentCount, edgeCount i) + 3 * componentCount ≤
        3 * ∑ i : Fin componentCount, vertexCount i := by
    have h := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hlocal i
    simpa [Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm,
      Nat.mul_left_comm] using h
  omega

/-- The component combination has equality at its smallest numerical base. -/
theorem edgeBound_of_components_base : 3 ≤ 3 * (2 - 1) := by
  norm_num

/-- Average degree below six supplies a vertex of active degree at most five. -/
theorem exists_lowDegree_of_hereditaryAverageDegree
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (haverage : HasHereditaryAverageDegreeLtSix incident)
    (vertices : Finset V) (edges : Finset E)
    (hcovered : EdgesCovered incident vertices edges)
    (hvertices : vertices.Nonempty) :
    ∃ x ∈ vertices, (incidentEdges incident x edges).card ≤ 5 := by
  by_contra hnone
  have hdegree : ∀ x ∈ vertices,
      6 ≤ (incidentEdges incident x edges).card := by
    intro x hx
    have hnot : ¬ (incidentEdges incident x edges).card ≤ 5 := by
      intro hle
      exact hnone ⟨x, hx, hle⟩
    omega
  have hlower : 6 * vertices.card ≤
      ∑ x ∈ vertices, (incidentEdges incident x edges).card := by
    calc
      6 * vertices.card = ∑ _x ∈ vertices, 6 := by
        simp [Nat.mul_comm]
      _ ≤ ∑ x ∈ vertices, (incidentEdges incident x edges).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact hdegree x hx
  have hstrict := haverage vertices edges hcovered hvertices
  omega

/-- The hereditary Euler inequality gives a five-deletion order by finite
induction. -/
theorem exists_fiveDeletionOrder_of_hereditaryAverageDegree
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    (incident : V → E → Prop) [DecidableRel incident]
    (haverage : HasHereditaryAverageDegreeLtSix incident)
    (vertices : Finset V) (edges : Finset E)
    (hcovered : EdgesCovered incident vertices edges) :
    Nonempty (FiveDeletionOrder incident vertices edges) := by
  apply exists_fiveDeletionOrder_of_lowDegree incident
  · intro remainingVertices remainingEdges hremaining hnonempty
    exact exists_lowDegree_of_hereditaryAverageDegree incident haverage
      remainingVertices remainingEdges hremaining hnonempty
  · exact hcovered

/-- The weighted conclusion of Osin's Appendix Lemma `Eul` along a
five-deletion order. -/
theorem edgeWeight_sum_le_of_fiveDeletionOrder
    {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]
    {incident : V → E → Prop} [DecidableRel incident]
    {vertices : Finset V} {edges : Finset E}
    (order : FiveDeletionOrder incident vertices edges)
    (a : ℝ) (ha : 0 ≤ a) (vertexWeight : V → ℝ)
    (edgeWeight : E → ℝ)
    (hvertex : ∀ x, 0 ≤ vertexWeight x)
    (hedge : ∀ x e, incident x e → edgeWeight e ≤ a * vertexWeight x) :
    (∑ e ∈ edges, edgeWeight e) ≤
      5 * a * ∑ x ∈ vertices, vertexWeight x := by
  classical
  induction order with
  | empty => simp
  | @step vertices edges x hx hdegree tail ih =>
      have hactiveNonneg : 0 ≤ a * vertexWeight x :=
        mul_nonneg ha (hvertex x)
      have hactive :
          (∑ e ∈ incidentEdges incident x edges, edgeWeight e) ≤
            5 * (a * vertexWeight x) := by
        calc
          (∑ e ∈ incidentEdges incident x edges, edgeWeight e) ≤
              ∑ _e ∈ incidentEdges incident x edges,
                a * vertexWeight x := by
            apply Finset.sum_le_sum
            intro e he
            have he' : e ∈ edges ∧ incident x e := by
              simpa only [incidentEdges, Finset.mem_filter] using he
            exact hedge x e he'.2
          _ = ((incidentEdges incident x edges).card : ℝ) *
              (a * vertexWeight x) := by simp
          _ ≤ 5 * (a * vertexWeight x) := by
            apply mul_le_mul_of_nonneg_right _ hactiveNonneg
            exact_mod_cast hdegree
      have hsplit := Finset.sum_filter_add_sum_filter_not edges
        (fun e => incident x e) edgeWeight
      have hverticesSplit :
          (∑ y ∈ remainingVertices x vertices, vertexWeight y) + vertexWeight x =
            ∑ y ∈ vertices, vertexWeight y := by
        simpa only [remainingVertices] using
          Finset.sum_erase_add vertices vertexWeight hx
      calc
        (∑ e ∈ edges, edgeWeight e) =
            (∑ e ∈ incidentEdges incident x edges, edgeWeight e) +
              ∑ e ∈ nonincidentEdges incident x edges, edgeWeight e := by
          change (∑ e ∈ edges, edgeWeight e) =
            (∑ e ∈ edges.filter (fun e => incident x e), edgeWeight e) +
              ∑ e ∈ edges.filter (fun e => ¬ incident x e), edgeWeight e
          exact hsplit.symm
        _ ≤ 5 * (a * vertexWeight x) +
            5 * a * ∑ y ∈ remainingVertices x vertices, vertexWeight y :=
          add_le_add hactive ih
        _ = 5 * a * ∑ y ∈ vertices, vertexWeight y := by
          rw [← hverticesSplit]
          ring

/-! ## Incidence deletion for combinatorial maps -/

namespace CombMap

/-- A connected planar combinatorial map whose face degrees are at least
three satisfies the edge inequality used for each nontrivial deletion
component in Osin's Lemma `Eul`. -/
theorem edgeCount_le_three_mul_vertex_sub_one
    (M : CombMap) (hplanar : M.IsPlanar)
    (hface : ∀ face : M.Face, 3 ≤ M.faceDegree face) :
    M.edgeCount ≤ 3 * (M.vertexCount - 1) := by
  classical
  have hEulerInt : (M.vertexCount : ℤ) + (M.faceCount : ℤ) =
      (M.edgeCount : ℤ) + 2 := by
    have h := M.euler_eq_two hplanar
    linarith
  have hEuler : M.vertexCount + M.faceCount = M.edgeCount + 2 := by
    exact_mod_cast hEulerInt
  have hfaceSum : 3 * M.faceCount ≤ 2 * M.edgeCount := by
    calc
      3 * M.faceCount = ∑ _face : M.Face, 3 := by
        simp [faceCount, Nat.mul_comm]
      _ ≤ ∑ face : M.Face, M.faceDegree face := by
        exact Finset.sum_le_sum fun face _ => hface face
      _ = 2 * M.edgeCount := M.sum_faceDegree_eq_two_mul_edgeCount
  omega

/-- A map vertex and edge are incident when a dart represents both. -/
def Incident (M : CombMap) (x : M.Vertex) (e : M.Edge) : Prop :=
  ∃ d : M.Dart, M.vertexOf d = x ∧ M.edgeOf d = e

noncomputable local instance vertexDecidableEq (M : CombMap) :
    DecidableEq M.Vertex :=
  Classical.decEq M.Vertex

noncomputable local instance edgeDecidableEq (M : CombMap) :
    DecidableEq M.Edge :=
  Classical.decEq M.Edge

noncomputable local instance incidentDecidable (M : CombMap) :
    DecidableRel M.Incident :=
  fun _ _ => Classical.propDecidable _

/-- Every edge of a combinatorial map is covered by the full vertex set. -/
theorem edgesCovered_univ (M : CombMap) :
    EdgesCovered M.Incident Finset.univ Finset.univ := by
  classical
  intro e _
  refine Quotient.inductionOn' e ?_
  intro d
  exact ⟨M.vertexOf d, Finset.mem_univ _, d, rfl, rfl⟩

/-- An edge of a combinatorial map has at most the vertices of its two
representing darts as endpoints. -/
theorem hasAtMostTwoEndpoints (M : CombMap) :
    HasAtMostTwoEndpoints M.Incident := by
  classical
  intro vertices edge
  refine Quotient.inductionOn' edge ?_
  intro d
  have hsubset :
      (vertices.filter fun x => M.Incident x (M.edgeOf d)) ⊆
        {M.vertexOf d, M.vertexOf (M.alpha d)} := by
    intro x hx
    have hincident : M.Incident x (M.edgeOf d) := (Finset.mem_filter.mp hx).2
    obtain ⟨q, hqx, hqe⟩ := hincident
    have hpair : DartPairRel M.alpha q d :=
      (M.edgeOf_eq_iff q d).mp hqe
    rcases hpair with hqd | halpha
    · subst q
      simp [hqx]
    · have hq : q = M.alpha d := by
        have h := congrArg M.alpha halpha
        rw [M.alpha_involutive q] at h
        exact h
      subst q
      simp [hqx]
  exact le_trans (Finset.card_le_card hsubset) Finset.card_le_two

/-- The low-degree theorem for every remaining incidence state gives the
five-deletion order used by the estimating graph. -/
theorem exists_fiveDeletionOrder
    (M : CombMap)
    (hlow : ∀ (vertices : Finset M.Vertex) (edges : Finset M.Edge),
      EdgesCovered M.Incident vertices edges → vertices.Nonempty →
        ∃ x ∈ vertices,
          (incidentEdges M.Incident x edges).card ≤ 5) :
    Nonempty (FiveDeletionOrder M.Incident Finset.univ Finset.univ) := by
  classical
  exact exists_fiveDeletionOrder_of_lowDegree M.Incident hlow
    Finset.univ Finset.univ M.edgesCovered_univ

/-- A hereditary average-degree estimate for the deleted planar states gives
the map's five-deletion order. -/
theorem exists_fiveDeletionOrder_of_hereditaryAverageDegree
    (M : CombMap) (haverage : HasHereditaryAverageDegreeLtSix M.Incident) :
    Nonempty (FiveDeletionOrder M.Incident Finset.univ Finset.univ) := by
  exact _root_.GroupApproximation.GGT.VanKampen.exists_fiveDeletionOrder_of_hereditaryAverageDegree
    M.Incident haverage Finset.univ Finset.univ M.edgesCovered_univ

/-- The componentwise planar edge inequality gives the full five-deletion
order for a combinatorial map. -/
theorem exists_fiveDeletionOrder_of_planarEdgeBound
    (M : CombMap) (hplanar : HasHereditaryPlanarEdgeBound M.Incident) :
    Nonempty (FiveDeletionOrder M.Incident Finset.univ Finset.univ) := by
  exact M.exists_fiveDeletionOrder_of_hereditaryAverageDegree
    (hereditaryAverageDegree_of_planarEdgeBound M.Incident
      M.hasAtMostTwoEndpoints hplanar)

/-- Osin's weighted Euler estimate once the planar deletion construction has
provided a five-deletion order. -/
theorem weighted_euler_of_fiveDeletionOrder
    (M : CombMap)
    (order : FiveDeletionOrder M.Incident Finset.univ Finset.univ)
    (a : ℝ) (ha : 0 ≤ a) (vertexWeight : M.Vertex → ℝ)
    (edgeWeight : M.Edge → ℝ)
    (hvertex : ∀ x, 0 ≤ vertexWeight x)
    (hedge : ∀ x e, M.Incident x e →
      edgeWeight e ≤ a * vertexWeight x) :
    (∑ e : M.Edge, edgeWeight e) ≤
      5 * a * ∑ x : M.Vertex, vertexWeight x := by
  simpa using
    edgeWeight_sum_le_of_fiveDeletionOrder order a ha vertexWeight edgeWeight
      hvertex hedge

end CombMap

end VanKampen
end GGT
end GroupApproximation
