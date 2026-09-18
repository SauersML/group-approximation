import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.TwoComplex.Reverse
import Mathlib.Algebra.Group.Action.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Group actions on ordered 2-complexes, and translation of edge paths

Lane `sk-leavitt-06`.  Khanh (arXiv:2609.08428v1), tex l.446: "The action of $G$ on ordered
$k$-frames is transitive"; tex l.460: "Every edge traversal is a translate of $E$ or its
reverse ... a passage across a triangle is a translate of the relation just computed."

`OrderedTwoComplex.Action X G` says that a given `MulAction G V` maps ordered edges to ordered
edges and ordered triangles to ordered triangles.  `EdgePath.translate hX g` is the image of an
edge path under `g`; it commutes with `append` and `reverse` and preserves homotopy.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

universe u

namespace OrderedTwoComplex

variable {V : Type u}

/-- The action of `G` on the vertices preserves ordered edges and ordered triangles. -/
structure Action (X : OrderedTwoComplex V) (G : Type*) [Group G] [MulAction G V] : Prop where
  /-- Translates of ordered edges are ordered edges. -/
  edge_smul : ∀ (g : G) {a b : V}, X.edge a b → X.edge (g • a) (g • b)
  /-- Translates of ordered triangles are ordered triangles. -/
  tri_smul : ∀ (g : G) {a b c : V}, X.tri a b c → X.tri (g • a) (g • b) (g • c)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.Action

variable {X : OrderedTwoComplex V} {G : Type*} [Group G] [MulAction G V]

theorem Action.edge_smul_iff (hX : X.Action G) (g : G) {a b : V} :
    X.edge (g • a) (g • b) ↔ X.edge a b := by
  refine ⟨fun h => ?_, hX.edge_smul g⟩
  have h' := hX.edge_smul g⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul] at h'

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.Action.edge_smul_iff

theorem Action.tri_smul_iff (hX : X.Action G) (g : G) {a b c : V} :
    X.tri (g • a) (g • b) (g • c) ↔ X.tri a b c := by
  refine ⟨fun h => ?_, hX.tri_smul g⟩
  have h' := hX.tri_smul g⁻¹ h
  rwa [inv_smul_smul, inv_smul_smul, inv_smul_smul] at h'

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.Action.tri_smul_iff

namespace EdgePath

/-- The translate of an edge path by `g`: each traversal of the ordered edge `(u,v)` becomes a
traversal, in the same direction, of the ordered edge `(g • u, g • v)`. -/
def translate (hX : X.Action G) (g : G) :
    {a b : V} → X.EdgePath a b → X.EdgePath (g • a) (g • b)
  | _, _, nil v => nil (g • v)
  | _, _, fwd e p => fwd (hX.edge_smul g e) (translate hX g p)
  | _, _, bwd e p => bwd (hX.edge_smul g e) (translate hX g p)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.translate

@[simp] theorem translate_nil (hX : X.Action G) (g : G) (v : V) :
    (nil v : X.EdgePath v v).translate hX g = nil (g • v) := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.translate_nil

@[simp] theorem translate_fwd (hX : X.Action G) (g : G) {a b c : V} (e : X.edge a b)
    (p : X.EdgePath b c) :
    (fwd e p).translate hX g = fwd (hX.edge_smul g e) (p.translate hX g) := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.translate_fwd

@[simp] theorem translate_bwd (hX : X.Action G) (g : G) {a b c : V} (e : X.edge b a)
    (p : X.EdgePath b c) :
    (bwd e p).translate hX g = bwd (hX.edge_smul g e) (p.translate hX g) := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.translate_bwd

theorem translate_append (hX : X.Action G) (g : G) :
    ∀ {a b c : V} (p : X.EdgePath a b) (q : X.EdgePath b c),
      (p.append q).translate hX g = (p.translate hX g).append (q.translate hX g)
  | _, _, _, nil _, _ => rfl
  | _, _, _, fwd e p, q => congrArg (fwd (hX.edge_smul g e)) (translate_append hX g p q)
  | _, _, _, bwd e p, q => congrArg (bwd (hX.edge_smul g e)) (translate_append hX g p q)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.translate_append

theorem translate_reverse (hX : X.Action G) (g : G) :
    ∀ {a b : V} (p : X.EdgePath a b), p.reverse.translate hX g = (p.translate hX g).reverse
  | _, _, nil _ => rfl
  | _, _, fwd e p => by
      rw [reverse_fwd, translate_append, translate_reverse hX g p, translate_fwd, reverse_fwd,
        translate_bwd, translate_nil]
  | _, _, bwd e p => by
      rw [reverse_bwd, translate_append, translate_reverse hX g p, translate_bwd, reverse_bwd,
        translate_fwd, translate_nil]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.translate_reverse

theorem Move.translate (hX : X.Action G) (g : G) {a b : V} {p q : X.EdgePath a b}
    (h : Move p q) : Move (p.translate hX g) (q.translate hX g) := by
  cases h with
  | backtrackFwd s e r =>
      simp only [translate_append]
      exact Move.backtrackFwd (s.translate hX g) (hX.edge_smul g e) (r.translate hX g)
  | backtrackBwd s e r =>
      simp only [translate_append]
      exact Move.backtrackBwd (s.translate hX g) (hX.edge_smul g e) (r.translate hX g)
  | triangle s t r =>
      simp only [translate_append]
      exact Move.triangle (s.translate hX g) (hX.tri_smul g t) (r.translate hX g)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.Move.translate

/-- Translation by a group element preserves homotopy of edge paths. -/
theorem Homotopic.translate (hX : X.Action G) (g : G) {a b : V} {p q : X.EdgePath a b}
    (h : Homotopic p q) : Homotopic (p.translate hX g) (q.translate hX g) := by
  have h' : Relation.EqvGen Move p q := h
  clear h
  induction h' with
  | rel _ _ hm => exact (hm.translate hX g).homotopic
  | refl _ => exact Homotopic.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.Homotopic.translate

end EdgePath

end OrderedTwoComplex

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
