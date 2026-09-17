import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.Frame.Complex
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.TwoComplex.Action
import GroupApproximation.Meta.AxiomGuard

/-!
# The ordered frame complex `X_n(A)` on frame vertices

Lane `sk-leavitt-07` (carto `sk-leavitt`).  Khanh (arXiv:2609.08428v1), tex l.424: "A
$(k-1)$-simplex ... is an ordered tuple $(v_1,\ldots,v_k)$ ... Faces delete a vector";
tex l.446: "The action of $G$ on ordered $k$-frames is transitive".

## Correction to the lane line

The lane line asks for `frameComplex A n : OrderedTwoComplex (Fin n → A)`.  On that vertex type
the complex is not connected (once `A ≠ 0` the zero vector lies on no edge frame, since a unit
has no zero column), so lane 10's `SimplyConnected` would fail.  Following the relay from lane
`sk-leavitt-10`, the vertex type here is `FrameVertices A n = {u // frameVertex u}`, the
unimodular vectors.  `Frame.FourBridge` identifies the case `n = 4` with lane 10's
`FrameFan.frameComplexFour`.

* `frameComplex A n`: ordered edges are the ordered 2-frames and ordered triangles the ordered
  3-frames.
* `frameComplex_action`: `GL_n(A)` acts on the frame vertices and preserves edges and triangles.
* `frame_transitive_vertex`, `frame_transitive_edge`, `frame_transitive_tri`: transitivity on
  vertices, ordered edges and ordered triangles.  `IsFrame.exists_smul_eq` gives it for every
  `k`, and `frame_transitive_k` restates it.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

variable {A : Type*} [Ring A] {n : ℕ}

/-- The vertices of `X_n(A)`: the unimodular vectors (1-frames) of `A^n`. -/
abbrev FrameVertices (A : Type*) [Ring A] (n : ℕ) : Type _ := {u : Fin n → A // frameVertex u}

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FrameVertices

/-- `GL_n(A)` acts on the frame vertices. -/
instance frameVerticesMulAction : MulAction (Matrix (Fin n) (Fin n) A)ˣ (FrameVertices A n) where
  smul g u := ⟨g • u.1, u.2.smul g⟩
  one_smul u := Subtype.ext (one_smul _ u.1)
  mul_smul g h u := Subtype.ext (mul_smul g h u.1)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVerticesMulAction

theorem frameVertices_smul_val (g : (Matrix (Fin n) (Fin n) A)ˣ) (u : FrameVertices A n) :
    (g • u).1 = g • u.1 := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameVertices_smul_val

/-- The ordered frame complex `X_n(A)` on frame vertices: ordered edges are the ordered 2-frames,
ordered triangles the ordered 3-frames. -/
def frameComplex (A : Type*) [Ring A] (n : ℕ) : OrderedTwoComplex (FrameVertices A n) where
  edge u v := frameEdge u.1 v.1
  tri u v w := frameTri u.1 v.1 w.1
  tri_edge01 h := frameTri.edge01 h
  tri_edge12 h := frameTri.edge12 h
  tri_edge02 h := frameTri.edge02 h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplex

theorem frameComplex_edge (u v : FrameVertices A n) :
    (frameComplex A n).edge u v = frameEdge u.1 v.1 := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplex_edge

theorem frameComplex_tri (u v w : FrameVertices A n) :
    (frameComplex A n).tri u v w = frameTri u.1 v.1 w.1 := rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplex_tri

/-- `GL_n(A)` preserves ordered edges and ordered triangles of `X_n(A)`. -/
theorem frameComplex_action : (frameComplex A n).Action (Matrix (Fin n) (Fin n) A)ˣ where
  edge_smul := fun g {_ _} h => frameEdge.smul h g
  tri_smul := fun g {_ _ _} h => frameTri.smul h g

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frameComplex_action

/-- `GL_n(A)` acts transitively on ordered `k`-frames (for every `k`, in particular `k ≤ 3`). -/
theorem frame_transitive_k {k : ℕ} {v w : Fin k → Fin n → A} (hv : IsFrame v) (hw : IsFrame w) :
    ∃ g : (Matrix (Fin n) (Fin n) A)ˣ, ∀ i, g • v i = w i :=
  hv.exists_smul_eq hw

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_transitive_k

theorem frame_transitive_vertex (u v : FrameVertices A n) :
    ∃ g : (Matrix (Fin n) (Fin n) A)ˣ, g • u = v := by
  obtain ⟨g, hg⟩ := frame_transitive_k u.2 v.2
  have h0 : g • u.1 = v.1 := hg 0
  exact ⟨g, Subtype.ext h0⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_transitive_vertex

theorem frame_transitive_edge {a b c d : FrameVertices A n} (hab : (frameComplex A n).edge a b)
    (hcd : (frameComplex A n).edge c d) :
    ∃ g : (Matrix (Fin n) (Fin n) A)ˣ, g • a = c ∧ g • b = d := by
  obtain ⟨g, hg⟩ := frame_transitive_k (show frameEdge a.1 b.1 from hab)
    (show frameEdge c.1 d.1 from hcd)
  have h0 : g • a.1 = c.1 := hg 0
  have h1 : g • b.1 = d.1 := hg 1
  exact ⟨g, Subtype.ext h0, Subtype.ext h1⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_transitive_edge

theorem frame_transitive_tri {a b c a' b' c' : FrameVertices A n}
    (h : (frameComplex A n).tri a b c) (h' : (frameComplex A n).tri a' b' c') :
    ∃ g : (Matrix (Fin n) (Fin n) A)ˣ, g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  obtain ⟨g, hg⟩ := frame_transitive_k (show frameTri a.1 b.1 c.1 from h)
    (show frameTri a'.1 b'.1 c'.1 from h')
  have h0 : g • a.1 = a'.1 := hg 0
  have h1 : g • b.1 = b'.1 := hg 1
  have h2 : g • c.1 = c'.1 := hg 2
  exact ⟨g, Subtype.ext h0, Subtype.ext h1, Subtype.ext h2⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.frame_transitive_tri

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
