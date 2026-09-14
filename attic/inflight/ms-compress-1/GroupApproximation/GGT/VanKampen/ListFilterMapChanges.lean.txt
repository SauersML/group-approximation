import GroupApproximation.GGT.VanKampen.ListNoABABChanges
import GroupApproximation.Meta.AxiomGuard

/-!
# Letter changes read through a partial map

Read a word from positions `0, …, n − 1` through a partial map `f : ℕ → Option α`, skipping the
positions where `f` is undefined: `(range n).filterMap f`.  Two consecutive positions `s`, `s + 1`
where `f` is defined with different values are two consecutive letters of the word, so they give
a letter change.

This is the reading of a polygon walk in the contact count of Osin's Lemma 9.4: positions are the
sides, `f` is the object across a side, and a change at consecutive sides is an object change.

* `ListNoABAB.adjChanges_append_singleton`: appending a letter adds one change when it differs
  from the last letter.
* `ListNoABAB.getLast?_filterMap_range_succ`: the last letter is the value at the last position.
* `ListNoABAB.card_consecutiveChanges_le`: the consecutive changes number at most `adjChanges` of
  the word.

## Manuscript status

Infrastructure for `thm:hull` (through the contact count of Osin's Lemma 9.4,
arXiv:math/0411039v3, §9); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.ListNoABAB

open List

variable {α : Type*} [DecidableEq α]

/-- **Appending a letter adds one change when it differs from the last letter.** -/
theorem adjChanges_append_singleton : ∀ (L : List α) (y : α) (hL : L ≠ []),
    adjChanges (L ++ [y]) = adjChanges L + (if L.getLast hL ≠ y then 1 else 0)
  | [], _, hL => absurd rfl hL
  | [a], y, _ => by
    show (if a ≠ y then 1 else 0) + 0 = 0 + (if a ≠ y then 1 else 0)
    omega
  | a :: b :: l, y, _ => by
    have ih := adjChanges_append_singleton (b :: l) y (List.cons_ne_nil b l)
    show (if a ≠ b then 1 else 0) + adjChanges ((b :: l) ++ [y]) =
      ((if a ≠ b then 1 else 0) + adjChanges (b :: l)) +
        (if (a :: b :: l).getLast (List.cons_ne_nil _ _) ≠ y then 1 else 0)
    rw [ih, List.getLast_cons (List.cons_ne_nil b l)]
    omega

theorem adjChanges_le_append_singleton (L : List α) (y : α) :
    adjChanges L ≤ adjChanges (L ++ [y]) := by
  by_cases hL : L = []
  · subst hL
    exact Nat.zero_le _
  · rw [adjChanges_append_singleton L y hL]
    omega

/-- **The last letter is the value at the last position.** -/
theorem getLast?_filterMap_range_succ (f : ℕ → Option α) (n : ℕ) {x : α} (hx : f n = some x) :
    ((List.range (n + 1)).filterMap f).getLast? = some x := by
  rw [List.range_succ, List.filterMap_append]
  simp [hx]

/-- The consecutive positions where `f` is defined with different values. -/
noncomputable def consecutiveChanges (f : ℕ → Option α) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun s => s + 1 < n ∧ ∃ x y, f s = some x ∧ f (s + 1) = some y ∧ x ≠ y

/-- **The consecutive changes number at most the letter changes of the word read.** -/
theorem card_consecutiveChanges_le (f : ℕ → Option α) :
    ∀ n : ℕ, (consecutiveChanges f n).card ≤ adjChanges ((List.range n).filterMap f)
  | 0 => by simp [consecutiveChanges]
  | n + 1 => by
    have ih := card_consecutiveChanges_le f n
    -- the old changes, and possibly the change at `n − 1`
    have hsub : consecutiveChanges f (n + 1) ⊆
        consecutiveChanges f n ∪ ((Finset.range (n + 1)).filter fun s =>
          s + 1 = n ∧ ∃ x y, f s = some x ∧ f (s + 1) = some y ∧ x ≠ y) := by
      intro s hs
      simp only [consecutiveChanges, Finset.mem_filter, Finset.mem_range] at hs
      obtain ⟨hsn, hlt, hxy⟩ := hs
      by_cases he : s + 1 = n
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsn, he, hxy⟩)
      · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_, hxy⟩)
        · omega
        · omega
    rw [List.range_succ, List.filterMap_append]
    cases hfn : f n with
    | none =>
      simp only [List.filterMap_cons, hfn, List.filterMap_nil, List.append_nil]
      have hextra : ((Finset.range (n + 1)).filter fun s =>
          s + 1 = n ∧ ∃ x y, f s = some x ∧ f (s + 1) = some y ∧ x ≠ y) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
        obtain ⟨-, he, x, y, -, hy, -⟩ := Finset.mem_filter.mp hs
        rw [he, hfn] at hy
        exact absurd hy (by simp)
      rw [hextra, Finset.union_empty] at hsub
      exact (Finset.card_le_card hsub).trans ih
    | some y =>
      simp only [List.filterMap_cons, hfn, List.filterMap_nil]
      by_cases hc : ∃ x, n ≠ 0 ∧ f (n - 1) = some x ∧ x ≠ y
      · obtain ⟨x, hn0, hx, hxy⟩ := hc
        have hlast : ((List.range n).filterMap f).getLast? = some x := by
          have e := getLast?_filterMap_range_succ f (n - 1) hx
          rwa [show n - 1 + 1 = n by omega] at e
        have hL : (List.range n).filterMap f ≠ [] := fun h => by simp [h] at hlast
        have hget : ((List.range n).filterMap f).getLast hL = x := by
          rw [List.getLast?_eq_some_getLast hL] at hlast
          exact Option.some_injective _ hlast
        rw [adjChanges_append_singleton _ y hL, hget, if_pos hxy]
        have hone : ((Finset.range (n + 1)).filter fun s =>
            s + 1 = n ∧ ∃ x y, f s = some x ∧ f (s + 1) = some y ∧ x ≠ y).card ≤ 1 := by
          refine Finset.card_le_one.mpr fun s hs t ht => ?_
          have h1 := (Finset.mem_filter.mp hs).2.1
          have h2 := (Finset.mem_filter.mp ht).2.1
          omega
        exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
      · have hextra : ((Finset.range (n + 1)).filter fun s =>
            s + 1 = n ∧ ∃ x y, f s = some x ∧ f (s + 1) = some y ∧ x ≠ y) = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun s hs => ?_
          obtain ⟨-, he, x, y', hx, hy', hxy'⟩ := Finset.mem_filter.mp hs
          rw [he, hfn] at hy'
          obtain rfl := Option.some_injective _ hy'
          exact hc ⟨x, by omega, by rwa [show n - 1 = s by omega], hxy'⟩
        rw [hextra, Finset.union_empty] at hsub
        exact (Finset.card_le_card hsub).trans (ih.trans (adjChanges_le_append_singleton _ _))

end GroupApproximation.GGT.VanKampen.ListNoABAB

#audit_axioms GroupApproximation.GGT.VanKampen.ListNoABAB.adjChanges_append_singleton
#audit_axioms GroupApproximation.GGT.VanKampen.ListNoABAB.card_consecutiveChanges_le
