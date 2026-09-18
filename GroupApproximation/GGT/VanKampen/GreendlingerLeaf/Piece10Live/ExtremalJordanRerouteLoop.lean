import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.ExtremalArcEndExistsParity
import GroupApproximation.Meta.AxiomGuard

/-!
# The parity count with loop darts

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-30.

The parity lemma `extremalArcEndExists_closed_run` (lane gl-p10-25) closes a removed gap `B`
between kept darts `d`, `e` of a boundary cycle when every other dart is kept.  Here the
hypothesis on the darts outside the gap is weakened: each of them is kept **or a loop**
(`vertexOf x = vertexOf (alpha x)`).  A loop dart has edge weight zero at every vertex
(`extremalJordanReroute_weight_eq_zero`), so the count is unchanged
(`extremalJordanReroute_closed_run_loops`).

Also: a gap made only of loop darts is linked by the walk chain alone
(`extremalJordanReroute_chain_loops`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

universe v

open Embedded Surgery.MapCollapse SimpleClosedWalkSides P10Rose.FilterMove P10Rose.SubArcMove

/-- **A kept dart or a loop dart has edge weight zero** at every vertex. -/
theorem extremalJordanReroute_weight_eq_zero (M : CombMap.{v}) (z : M.Dart → Bool)
    (w : M.Vertex) {x : M.Dart}
    (hx : movePred M z x = true ∨ M.vertexOf x = M.vertexOf (M.alpha x)) :
    extremalArcEndExists_weight M z (extremalArcEndExists_at M w) x = 0 := by
  rcases hx with hx | hx
  · obtain ⟨h1, h2⟩ := (movePred_eq_true_iff M z x).mp hx
    unfold extremalArcEndExists_weight
    rw [h1, h2, extremalArcEndExists_add_self (extremalArcEndExists_col false), mul_zero]
  · unfold extremalArcEndExists_weight
    rw [extremalArcEndExists_at_congr M w hx,
      extremalArcEndExists_add_self (extremalArcEndExists_at M w (M.alpha x)), zero_mul]

/-- **A lone removed run is closed, with loops allowed outside it**: if every dart of the
boundary cycle outside the gap `B` between the kept darts `d` and `e` is kept or a loop, and
every dart of `B` is removed, then `α d` and `e` share a vertex.  Parity count at the vertex of
`e`, as in `extremalArcEndExists_closed_run`. -/
theorem extremalJordanReroute_closed_run_loops (M : CombMap.{v}) {faces : Finset M.Face}
    {c : List M.Dart} (hc : ∀ d, d ∈ c ↔ Surgery.MapCollapse.IsBoundaryDart M faces d)
    (hnd : c.Nodup) (hchain : c.IsChain fun a b => M.vertexOf (M.alpha a) = M.vertexOf b)
    (z : M.Dart → Bool) (hz : ∀ x y, CombMap.FaceClassStep M (walkKeep M c) x y → z x = z y)
    (hind : ∀ d ∈ c, z d = false ∨ z (M.alpha d) = false)
    {A B C : List M.Dart} {d e : M.Dart} (hdec : c = A ++ d :: (B ++ e :: C))
    (hA : ∀ x ∈ A, movePred M z x = true ∨ M.vertexOf x = M.vertexOf (M.alpha x))
    (hd : movePred M z d = true)
    (hB : ∀ x ∈ B, movePred M z x = false) (he : movePred M z e = true)
    (hC : ∀ x ∈ C, movePred M z x = true ∨ M.vertexOf x = M.vertexOf (M.alpha x)) :
    M.vertexOf (M.alpha d) = M.vertexOf e := by
  have hremoved : ∀ x ∈ B,
      extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e)) x =
        extremalArcEndExists_at M (M.vertexOf e) x +
          extremalArcEndExists_at M (M.vertexOf e) (M.alpha x) := by
    intro x hx
    have hxc : x ∈ c := by
      rw [hdec]
      simp [hx]
    unfold extremalArcEndExists_weight
    rw [extremalArcEndExists_col_removed (a := z x) (b := z (M.alpha x)) (hB x hx)
      (hind x hxc), mul_one]
  have hsum := extremalArcEndExists_parity M hc hnd z hz
    (extremalArcEndExists_at M (M.vertexOf e)) (extremalArcEndExists_at_sigma M (M.vertexOf e))
  have hch : (d :: (B ++ [e])).IsChain fun a b => M.vertexOf (M.alpha a) = M.vertexOf b :=
    hchain.infix ⟨A, C, by
      rw [hdec]
      simp⟩
  have hT := extremalArcEndExists_telescope M (M.vertexOf e) e B d hch
  rw [hdec, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append, List.map_cons, List.sum_cons,
    extremalArcEndExists_sum_map_eq_zero
      (extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e))) A
      (fun x hx => extremalJordanReroute_weight_eq_zero M z (M.vertexOf e) (hA x hx)),
    extremalJordanReroute_weight_eq_zero M z (M.vertexOf e) (Or.inl hd),
    extremalJordanReroute_weight_eq_zero M z (M.vertexOf e) (Or.inl he),
    extremalArcEndExists_sum_map_eq_zero
      (extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e))) C
      (fun x hx => extremalJordanReroute_weight_eq_zero M z (M.vertexOf e) (hC x hx)),
    extremalArcEndExists_sum_map_congr
      (extremalArcEndExists_weight M z (extremalArcEndExists_at M (M.vertexOf e)))
      (fun x => extremalArcEndExists_at M (M.vertexOf e) x +
        extremalArcEndExists_at M (M.vertexOf e) (M.alpha x)) B hremoved,
    hT, extremalArcEndExists_at_eq_one M (rfl : M.vertexOf e = M.vertexOf e)] at hsum
  simp only [zero_add, add_zero] at hsum
  exact extremalArcEndExists_vertexOf_of_at M (extremalArcEndExists_eq_one_of_add_one _ hsum)

/-- **A gap of loop darts is linked** by the walk chain: along `d, B, e` with every dart of `B`
a loop, `α d` and `e` share a vertex. -/
theorem extremalJordanReroute_chain_loops (M : CombMap.{v}) (e : M.Dart) (B : List M.Dart) :
    ∀ d : M.Dart,
      (d :: (B ++ [e])).IsChain (fun a b => M.vertexOf (M.alpha a) = M.vertexOf b) →
        (∀ x ∈ B, M.vertexOf x = M.vertexOf (M.alpha x)) →
          M.vertexOf (M.alpha d) = M.vertexOf e := by
  induction B with
  | nil =>
    intro d h _
    rw [List.nil_append] at h
    exact (List.isChain_cons_cons.mp h).1
  | cons b B ih =>
    intro d h hl
    rw [List.cons_append] at h
    obtain ⟨h1, h2⟩ := List.isChain_cons_cons.mp h
    exact h1.trans ((hl b List.mem_cons_self).trans
      (ih b h2 fun x hx => hl x (List.mem_cons_of_mem b hx)))

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_weight_eq_zero
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_closed_run_loops
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.extremalJordanReroute_chain_loops
