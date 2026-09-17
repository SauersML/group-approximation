import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.TwoComplex.Homotopy
import GroupApproximation.Meta.AxiomGuard

/-!
# The fan argument: a cone apex for vertices and edges gives simple connectivity

Lane `sk-leavitt-10`.  Khanh (arXiv:2609.08428v1), tex l.539: "any finite collection of vertices
and edges has a common apex ... Coning a pair of vertices produces a path between them. For a
finite edge loop, choose one such apex $v$. For each ordered edge $(u,w)$ traversed by the loop,
use the triangle $(v,u,w)$. Adjacent triangles share the radial edge $(v,u)$, so they glue to a
continuous triangular fan whose boundary is the prescribed loop. A reverse traversal uses the same
ordered edge and its triangle with reverse orientation; it does not replace that edge by the
distinct cell $(w,u)$."

## Route

Everything is stated for an abstract `OrderedTwoComplex` of lane `sk-leavitt-06`
(`TwoComplex.Basic`, `TwoComplex.Homotopy`), whose `SimplyConnected` is connectedness plus
null-homotopy of every edge loop by backtracking and triangle passages.

* `FrameFan.edges p`: the ordered edge cells traversed by `p` (a backward traversal of the cell
  `(w,u)` records `(w,u)`, not `(u,w)`).
* `FrameFan.HasFanApex X`: every finite list of vertices and of ordered edges has one apex `c`
  with `(c,u)` an edge for each listed vertex and `(c,u,w)` a triangle for each listed edge.
* `FrameFan.homotopic_fan`: if every traversed cell `(u,w)` of `p : a ⟶ b` spans a triangle
  `(c,u,w)`, then `p ≃ (c,a)⁻¹·(c,b)`.  Induction on `p`; a forward step uses one passage across
  `(c,u,w)`, a backward step uses `homotopic_triangle_fwd02_bwd12` across the same triangle.
* `FrameFan.simplyConnected_of_hasFanApex`: coning `[a, b]` joins `a` to `b`; coning `[v]` and
  `edges loop` contracts the loop to the backtrack `(c,v)⁻¹·(c,v) ≃ nil`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan

open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath

universe u

variable {V : Type u} {X : OrderedTwoComplex V}

/-- The ordered edge cells traversed by an edge path, in order. -/
def edges : {a b : V} → X.EdgePath a b → List (V × V)
  | _, _, nil _ => []
  | _, _, fwd (a := a) (b := b) _ p => (a, b) :: edges p
  | _, _, bwd (a := a) (b := b) _ p => (b, a) :: edges p

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.edges

theorem edges_nil (v : V) : edges (nil v : X.EdgePath v v) = [] := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.edges_nil

theorem edges_fwd {a b d : V} (e : X.edge a b) (p : X.EdgePath b d) :
    edges (fwd e p) = (a, b) :: edges p := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.edges_fwd

theorem edges_bwd {a b d : V} (e : X.edge b a) (p : X.EdgePath b d) :
    edges (bwd e p) = (b, a) :: edges p := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.edges_bwd

/-- Every recorded cell of an edge path is an ordered edge. -/
theorem edges_edge : ∀ {a b : V} (p : X.EdgePath a b), ∀ x ∈ edges p, X.edge x.1 x.2
  | _, _, nil _, _, hx => by
      rw [edges_nil] at hx
      simp at hx
  | _, _, fwd (a := a) (b := b) e p, x, hx => by
      rw [edges_fwd] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact e
      · exact edges_edge p x hx
  | _, _, bwd (a := a) (b := b) e p, x, hx => by
      rw [edges_bwd] at hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact e
      · exact edges_edge p x hx

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.edges_edge

/-- The cone property of tex l.539: any finite list of vertices and ordered edges has a common
apex, joined by an edge to each listed vertex and spanning a triangle with each listed edge. -/
def HasFanApex (X : OrderedTwoComplex V) : Prop :=
  ∀ (vs : List V) (es : List (V × V)), (∀ x ∈ es, X.edge x.1 x.2) →
    ∃ c : V, (∀ w ∈ vs, X.edge c w) ∧ ∀ x ∈ es, X.tri c x.1 x.2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.HasFanApex

/-- The fan: an edge path whose traversed cells `(u,w)` all span triangles `(c,u,w)` is
homotopic to the two radial edges `(c,a)⁻¹·(c,b)`. -/
theorem homotopic_fan (c : V) : ∀ {a b : V} (p : X.EdgePath a b) (hca : X.edge c a)
    (hcb : X.edge c b), (∀ x ∈ edges p, X.tri c x.1 x.2) →
    Homotopic p (bwd hca (fwd hcb (nil b)))
  | _, _, nil v, hca, _, _ => (homotopic_backtrackBwd hca (nil v)).symm
  | _, _, fwd (a := a) (b := a') e p, hca, hcb, ht => by
      have t : X.tri c a a' :=
        ht (a, a') (by rw [edges_fwd]; exact List.mem_cons.2 (Or.inl rfl))
      have hl : ∀ x ∈ edges p, X.tri c x.1 x.2 := fun x hx =>
        ht x (by rw [edges_fwd]; exact List.mem_cons_of_mem _ hx)
      exact ((homotopic_fan c p (X.tri_edge02 t) hcb hl).congr_fwd e).trans
        ((homotopic_backtrackBwd hca _).symm.trans
          (((homotopic_triangle t _).congr_bwd hca).trans
            ((homotopic_backtrackFwd (X.tri_edge02 t) _).congr_bwd hca)))
  | _, _, bwd (a := a) (b := a') e p, hca, hcb, ht => by
      have t : X.tri c a' a :=
        ht (a', a) (by rw [edges_bwd]; exact List.mem_cons.2 (Or.inl rfl))
      have hl : ∀ x ∈ edges p, X.tri c x.1 x.2 := fun x hx =>
        ht x (by rw [edges_bwd]; exact List.mem_cons_of_mem _ hx)
      exact ((homotopic_fan c p (X.tri_edge01 t) hcb hl).congr_bwd e).trans
        ((homotopic_backtrackBwd hca _).symm.trans
          (((homotopic_triangle_fwd02_bwd12 t _).congr_bwd hca).trans
            ((homotopic_backtrackFwd (X.tri_edge01 t) _).congr_bwd hca)))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.homotopic_fan

/-- Tex l.539: an ordered 2-complex with the cone property is simply connected. -/
theorem simplyConnected_of_hasFanApex (hX : HasFanApex X) : X.SimplyConnected := by
  refine ⟨fun a b => ?_, fun v p => ?_⟩
  · obtain ⟨c, hc, -⟩ := hX [a, b] [] (fun _ hx => by simp at hx)
    exact ⟨bwd (hc a (List.mem_cons.2 (Or.inl rfl)))
      (fwd (hc b (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))) (nil b))⟩
  · obtain ⟨c, hc, ht⟩ := hX [v] (edges p) (edges_edge p)
    have hcv : X.edge c v := hc v (List.mem_cons.2 (Or.inl rfl))
    exact (homotopic_fan c p hcv hcv ht).trans (homotopic_backtrackBwd hcv (nil v))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan.simplyConnected_of_hasFanApex

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameFan
