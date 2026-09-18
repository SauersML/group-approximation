import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.WitnessStepOrderList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, lane gl-p07-64: an order-preserving list is a sublist

Lane gl-p07-64.  A pure list lemma for `WitnessStepLobeStatement.lean`.  It certifies no printed
sentence on its own.  NOT COMPILED: authored without running Lean.

* `witnessStepLobe_sublist_of_before`: let `l` and `w` be duplicate-free lists, with every entry
  of `l` on `w`.  If every `c` before `d` in `l` is also before `d` in `w`, then `l <+ w`.

## Proof

Induction on `l = x :: l'`.  Split `w = u ++ x :: v`.  Every `y ∈ l'` is after `x` in `l`, so it is
after `x` in `w`.  It is not `x`, because `l` is duplicate free.  It is not in `u`, because then
`y` would come before `x` in `w`, and the order of `w` is asymmetric
(`witnessStepOrder_before_asymm`).  So `l' ⊆ v`.  The order of `w` on `v` is the order of `v`
(`witnessStepOrder_before_sublist_iff`).  The induction hypothesis gives `l' <+ v`, and then
`x :: l' <+ u ++ x :: v`.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket

namespace FourPieceWitness

/-- A later entry of a list is after its head. -/
theorem witnessStepLobe_before_cons {α : Type*} {x y : α} {l : List α} (hy : y ∈ l) :
    WitnessStepGenusBefore (x :: l) x y := by
  obtain ⟨v, z, hl⟩ := List.append_of_mem hy
  exact ⟨[], v, z, by rw [hl, List.nil_append]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_before_cons

/-- The order of a tail is the order of the list. -/
theorem witnessStepLobe_before_of_before_tail {α : Type*} {x c d : α} {l : List α}
    (h : WitnessStepGenusBefore l c d) : WitnessStepGenusBefore (x :: l) c d := by
  obtain ⟨u, v, z, hl⟩ := h
  exact ⟨x :: u, v, z, by rw [hl, List.cons_append]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_before_of_before_tail

/-- An entry of the prefix `u` of `u ++ x :: v` is before `x`. -/
theorem witnessStepLobe_before_of_mem_prefix {α : Type*} {x y : α} {u v : List α}
    (hy : y ∈ u) : WitnessStepGenusBefore (u ++ x :: v) y x := by
  obtain ⟨u₁, u₂, hu⟩ := List.append_of_mem hy
  exact ⟨u₁, u₂, v, by rw [hu, List.append_assoc, List.cons_append]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_before_of_mem_prefix

/-- **An order-preserving duplicate-free list is a sublist.**  If the entries of `l` lie on `w`,
both are duplicate free, and every pair in order in `l` is in order in `w`, then `l <+ w`. -/
theorem witnessStepLobe_sublist_of_before {α : Type*} {l : List α} :
    ∀ {w : List α}, l.Nodup → w.Nodup → (∀ x ∈ l, x ∈ w) →
      (∀ c ∈ l, ∀ d ∈ l, WitnessStepGenusBefore l c d → WitnessStepGenusBefore w c d) →
      l <+ w := by
  induction l with
  | nil =>
    intro w _ _ _ _
    exact List.nil_sublist w
  | cons x l ih =>
    intro w hl hw hmem hord
    have hxw : x ∈ w := hmem x (by simp)
    obtain ⟨u, v, hwuv⟩ := List.append_of_mem hxw
    subst hwuv
    have hx : x ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    have hvw : v <+ u ++ x :: v :=
      (List.sublist_cons_self x v).trans (List.sublist_append_right u _)
    have hv : ∀ y ∈ l, y ∈ v := by
      intro y hy
      have hb : WitnessStepGenusBefore (u ++ x :: v) x y :=
        hord x (by simp) y (by simp [hy]) (witnessStepLobe_before_cons hy)
      have hyw : y ∈ u ++ x :: v := hmem y (by simp [hy])
      rcases List.mem_append.mp hyw with hyu | hyxv
      · exact absurd (witnessStepLobe_before_of_mem_prefix hyu)
          (witnessStepOrder_before_asymm hw hb)
      · rcases List.mem_cons.mp hyxv with hyx | hyv
        · exact absurd (hyx ▸ hy) hx
        · exact hyv
    have hsub : l <+ v := by
      refine ih hl' (hvw.nodup hw) hv ?_
      intro c hc d hd hcd
      exact (witnessStepOrder_before_sublist_iff hw hvw (hv c hc) (hv d hd)).mp
        (hord c (by simp [hc]) d (by simp [hd]) (witnessStepLobe_before_of_before_tail hcd))
    exact (List.cons_sublist_cons.mpr hsub).trans (List.sublist_append_right u _)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.FourPieceWitness.witnessStepLobe_sublist_of_before

end FourPieceWitness

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket
