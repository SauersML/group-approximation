import Mathlib.Data.List.NodupEquivFin
import GroupApproximation.Meta.AxiomGuard

open scoped List

/-!
# Reading a list backwards inside another list

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex 2134, Hull's small cancellation theorem, through Osin's Lemma 9.7).

`reverse_map_sublist_of_pos`: if every entry `g L[i]` of a list sits in `w` at a position
`q i`, and these positions strictly decrease along `L`, then the reversed image of `L` is a
sublist of `w`.
-/

namespace GroupApproximation.Full.GL03BPinchOrder

/-- **Decreasing positions give a reversed sublist.**  If `w[q i] = g L[i]` for every index of
`L`, and `q` strictly decreases on the indices of `L`, then `(L.reverse.map g) <+ w`.  (Osin, proof
of Lemma 9.7(b); `thm:hull`.) -/
theorem reverse_map_sublist_of_pos {α β : Type*} (g : α → β) {L : List α} {w : List β}
    (q : ℕ → ℕ) (hqlt : ∀ i, i < L.length → q i < w.length)
    (hqget : ∀ i (hi : i < L.length), w[q i]'(hqlt i hi) = g L[i])
    (hmono : ∀ i j, i < j → j < L.length → q j < q i) :
    L.reverse.map g <+ w := by
  have hlen : (L.reverse.map g).length = L.length := by
    rw [List.length_map, List.length_reverse]
  let f : Fin (L.reverse.map g).length → Fin w.length := fun ix =>
    ⟨q (L.length - 1 - ix.1), hqlt _ (by have := ix.2; omega)⟩
  have hf : StrictMono f := by
    intro a b hab
    have ha := a.2
    have hb := b.2
    have hab' : a.1 < b.1 := hab
    show q (L.length - 1 - a.1) < q (L.length - 1 - b.1)
    exact hmono _ _ (by omega) (by omega)
  refine List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
    ⟨OrderEmbedding.ofStrictMono f hf, fun ix => ?_⟩
  change (L.reverse.map g).get ix = w.get (f ix)
  have hix := ix.2
  have hi : L.length - 1 - ix.1 < L.length := by omega
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_reverse]
  exact (hqget _ hi).symm

end GroupApproximation.Full.GL03BPinchOrder

#audit_axioms GroupApproximation.Full.GL03BPinchOrder.reverse_map_sublist_of_pos
