import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.TwoComplex.Homotopy
import GroupApproximation.Meta.AxiomGuard

/-!
# Reversal of edge paths up to homotopy

Lane `sk-leavitt-06`.  Khanh (arXiv:2609.08428v1), tex l.460: "Backtracking cancels inverse
words, and a passage across a triangle is a translate of the relation just computed."

* `homotopic_triangle_bwd`: the reverse passage `(b,c)⁻¹·(a,b)⁻¹ ≃ (a,c)⁻¹`, derived from one
  triangle move and backtracking.
* `Homotopic.congr_reverse`: reversal respects homotopy.
* `append_reverse_self`, `reverse_append_self`: a path followed by its reverse is null-homotopic.
* `SimplyConnected.homotopic`: in a simply connected complex any two edge paths with the same
  endpoints are homotopic.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

universe u

namespace OrderedTwoComplex

variable {V : Type u} {X : OrderedTwoComplex V}

namespace EdgePath

/-- Passage across one ordered triangle `(a,b,c)` along the reversed boundary:
`(b,c)⁻¹·(a,b)⁻¹ ≃ (a,c)⁻¹`. -/
theorem homotopic_triangle_bwd {a b c d : V} (t : X.tri a b c) (q : X.EdgePath a d) :
    Homotopic (bwd (X.tri_edge12 t) (bwd (X.tri_edge01 t) q)) (bwd (X.tri_edge02 t) q) := by
  have h1 : Homotopic q (fwd (X.tri_edge02 t) (bwd (X.tri_edge02 t) q)) :=
    (homotopic_backtrackFwd (X.tri_edge02 t) q).symm
  have h2 : Homotopic (fwd (X.tri_edge02 t) (bwd (X.tri_edge02 t) q))
      (fwd (X.tri_edge01 t) (fwd (X.tri_edge12 t) (bwd (X.tri_edge02 t) q))) :=
    (homotopic_triangle t (bwd (X.tri_edge02 t) q)).symm
  have h3 : Homotopic
      (bwd (X.tri_edge01 t) (fwd (X.tri_edge01 t) (fwd (X.tri_edge12 t) (bwd (X.tri_edge02 t) q))))
      (fwd (X.tri_edge12 t) (bwd (X.tri_edge02 t) q)) :=
    homotopic_backtrackBwd (X.tri_edge01 t) (fwd (X.tri_edge12 t) (bwd (X.tri_edge02 t) q))
  have h4 : Homotopic (bwd (X.tri_edge12 t) (fwd (X.tri_edge12 t) (bwd (X.tri_edge02 t) q)))
      (bwd (X.tri_edge02 t) q) :=
    homotopic_backtrackBwd (X.tri_edge12 t) (bwd (X.tri_edge02 t) q)
  exact ((((h1.trans h2).congr_bwd (X.tri_edge01 t)).trans h3).congr_bwd (X.tri_edge12 t)).trans h4

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.homotopic_triangle_bwd

/-- The reverse of an elementary move is a homotopy. -/
theorem Move.congr_reverse {a b : V} {p q : X.EdgePath a b} (h : Move p q) :
    Homotopic p.reverse q.reverse := by
  cases h with
  | backtrackFwd s e r =>
      simp only [reverse_append, reverse_fwd, reverse_bwd, append_assoc]
      exact (homotopic_backtrackFwd e s.reverse).append_left r.reverse
  | backtrackBwd s e r =>
      simp only [reverse_append, reverse_fwd, reverse_bwd, append_assoc]
      exact (homotopic_backtrackBwd e s.reverse).append_left r.reverse
  | triangle s t r =>
      simp only [reverse_append, reverse_fwd, append_assoc]
      exact (homotopic_triangle_bwd t s.reverse).append_left r.reverse

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.Move.congr_reverse

/-- Reversal respects homotopy. -/
theorem Homotopic.congr_reverse {a b : V} {p q : X.EdgePath a b} (h : Homotopic p q) :
    Homotopic p.reverse q.reverse := by
  have h' : Relation.EqvGen Move p q := h
  clear h
  induction h' with
  | rel _ _ hm => exact hm.congr_reverse
  | refl _ => exact Homotopic.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.Homotopic.congr_reverse

/-- A path followed by its reverse is null-homotopic. -/
theorem append_reverse_self : ∀ {a b : V} (p : X.EdgePath a b),
    Homotopic (p.append p.reverse) (nil a)
  | _, _, nil _ => Homotopic.refl _
  | _, _, fwd e p =>
      (((Homotopic.of_eq (append_assoc p p.reverse (bwd e (nil _))).symm).trans
          ((append_reverse_self p).append_right (bwd e (nil _)))).congr_fwd e).trans
        (homotopic_backtrackFwd e (nil _))
  | _, _, bwd e p =>
      (((Homotopic.of_eq (append_assoc p p.reverse (fwd e (nil _))).symm).trans
          ((append_reverse_self p).append_right (fwd e (nil _)))).congr_bwd e).trans
        (homotopic_backtrackBwd e (nil _))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.append_reverse_self

/-- The reverse of a path followed by the path is null-homotopic. -/
theorem reverse_append_self {a b : V} (p : X.EdgePath a b) :
    Homotopic (p.reverse.append p) (nil b) := by
  have h := append_reverse_self p.reverse
  rw [reverse_reverse] at h
  exact h

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.EdgePath.reverse_append_self

end EdgePath

/-- In a simply connected ordered 2-complex, any two edge paths with the same endpoints are
homotopic. -/
theorem SimplyConnected.homotopic (hX : X.SimplyConnected) {a b : V}
    (p q : X.EdgePath a b) : EdgePath.Homotopic p q :=
  (EdgePath.Homotopic.of_eq (EdgePath.append_nil p).symm).trans <|
    ((EdgePath.reverse_append_self q).symm.append_left p).trans <|
      (EdgePath.Homotopic.of_eq (EdgePath.append_assoc p q.reverse q).symm).trans <|
        (hX.2 a (p.append q.reverse)).append_right q

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.OrderedTwoComplex.SimplyConnected.homotopic

end OrderedTwoComplex

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
