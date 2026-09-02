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
  simp only [incidentEdges, Finset.filter_empty, Finset.card_empty]
  omega

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
