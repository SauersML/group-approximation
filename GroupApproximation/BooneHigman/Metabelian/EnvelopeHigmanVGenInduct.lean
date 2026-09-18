import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenStep
import GroupApproximation.Meta.AxiomGuard

/-!
# Every cone swap from the cone swaps of words of length at most `3`

`vgen_swapIn_of_short`: over an alphabet with two letters, a subgroup containing the cone swaps of
all incomparable words of length `≤ 3` contains the cone swaps of all incomparable words.

Route: induction on a bound `n + 1 ≥ 4` for both lengths (`vgen_step`).  Write a word of length
`n + 1` as `p ++ [x]` with `|p| = n`.
* One word of length `n + 1`, the other `w` of length `≤ n`: `w` is incomparable with `p`; take `u`
  of length `2` incomparable with `p` and `w` (`vgen_exists_avoid2`) and shorten by conjugating with
  `coneSwap p u` (`vgen_step_left`, `vgen_step_right`).
* Both of length `n + 1` with a common parent `p`: conjugate with `coneSwap p u`, `|u| = 1`.
* Both of length `n + 1` with parents `p ≠ q`: shorten the first word as above, reaching the case of
  one long word.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

theorem vgen_split_last {v : List X} {n : ℕ} (hv : v.length = n + 1) :
    ∃ p x, v = p ++ [x] ∧ p.length = n := by
  rcases List.eq_nil_or_concat v with h | ⟨p, x, h⟩
  · subst h
    simp only [List.length_nil] at hv
    omega
  · rw [List.concat_eq_append] at h
    subst h
    simp only [List.length_append, List.length_singleton] at hv
    exact ⟨p, x, rfl, by omega⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_split_last

variable [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))}

theorem vgen_step_left {n : ℕ} (hn : 3 ≤ n)
    (ih : ∀ v w : List X, v.length ≤ n → w.length ≤ n → VGenSwapIn G v w) {v w : List X}
    (hv : v.length ≤ n + 1) (hw : w.length ≤ n) : VGenSwapIn G v w := by
  rcases Nat.lt_or_ge v.length (n + 1) with hlt | hge
  · exact ih v w (by omega) hw
  obtain ⟨p, x, rfl, hp⟩ := vgen_split_last (le_antisymm hv hge)
  intro hvw hwv
  have hpw : ¬ p <+: w := by
    intro h
    have heq : p = w := h.eq_of_length (by have := h.length_le; omega)
    rw [← heq] at hwv
    exact hwv (List.prefix_append p [x])
  have hwp : ¬ w <+: p := fun h => hwv (List.prefix_append_of_prefix h)
  obtain ⟨u, hu, hup, hpu, huw, hwu⟩ := vgen_exists_avoid2 (by omega : 2 ≤ p.length) hwp
  exact vgen_shorten_left x hpu hup hpw hwp huw hwu (ih p u (by omega) (by omega))
    (ih (u ++ [x]) w (by simp only [List.length_append, List.length_singleton, hu]; omega) hw)
    hvw hwv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_step_left

theorem vgen_step_right {n : ℕ} (hn : 3 ≤ n)
    (ih : ∀ v w : List X, v.length ≤ n → w.length ≤ n → VGenSwapIn G v w) {v w : List X}
    (hv : v.length ≤ n) (hw : w.length ≤ n + 1) : VGenSwapIn G v w := by
  rcases Nat.lt_or_ge w.length (n + 1) with hlt | hge
  · exact ih v w hv (by omega)
  obtain ⟨q, z, rfl, hq⟩ := vgen_split_last (le_antisymm hw hge)
  intro hvw hwv
  have hqv : ¬ q <+: v := by
    intro h
    have heq : q = v := h.eq_of_length (by have := h.length_le; omega)
    rw [← heq] at hvw
    exact hvw (List.prefix_append q [z])
  have hvq : ¬ v <+: q := fun h => hvw (List.prefix_append_of_prefix h)
  obtain ⟨u, hu, huq, hqu, huv, hvu⟩ := vgen_exists_avoid2 (by omega : 2 ≤ q.length) hvq
  exact vgen_shorten_right z hqu huq hqv hvq huv hvu (ih q u (by omega) (by omega))
    (ih v (u ++ [z]) hv (by simp only [List.length_append, List.length_singleton, hu]; omega))
    hvw hwv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_step_right

end GroupApproximation.BooneHigman.Metabelian.Envelope
