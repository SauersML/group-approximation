import GroupApproximation.BooneHigman.V.Transitive
import GroupApproximation.Meta.AxiomGuard

/-!
# Short words avoiding given words

Word combinatorics for generating the cone swaps of `V_d` from short ones.

* `vgen_exists_avoid1`: a nonempty word is incomparable with some word of length `1`;
* `vgen_exists_avoid2`: a word `p` with `2 ≤ |p|` and a word `w` incomparable with `p` are both
  incomparable with some word of length `2`;
* `vgen_not_prefix_append_left`, `vgen_not_prefix_append_right`: extending a word incomparable
  with `w` keeps it incomparable with `w`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- A nonempty word is incomparable with some one-letter word. -/
theorem vgen_exists_avoid1 [Nontrivial X] {p : List X} (hp : p ≠ []) :
    ∃ u : List X, u.length = 1 ∧ ¬ u <+: p ∧ ¬ p <+: u := by
  obtain ⟨a, p', rfl⟩ := List.exists_cons_of_ne_nil hp
  obtain ⟨e, he⟩ := exists_ne a
  exact ⟨[e], rfl, not_prefix_cons_of_ne he [] p', not_prefix_cons_of_ne (Ne.symm he) p' []⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_exists_avoid1

/-- Two incomparable words, the first of length at least `2`, are incomparable with a common word
of length `2`. -/
theorem vgen_exists_avoid2 [Nontrivial X] {p w : List X} (hp : 2 ≤ p.length)
    (hwp : ¬ w <+: p) :
    ∃ u : List X, u.length = 2 ∧ ¬ u <+: p ∧ ¬ p <+: u ∧ ¬ u <+: w ∧ ¬ w <+: u := by
  rcases p with _ | ⟨a, _ | ⟨c, p2⟩⟩
  · simp at hp
  · simp at hp
  rcases w with _ | ⟨b, w1⟩
  · exact absurd List.nil_prefix hwp
  by_cases hab : b = a
  · obtain ⟨e, he⟩ := exists_ne a
    have he' : e ≠ b := by
      rw [hab]
      exact he
    exact ⟨[e, e], rfl, not_prefix_cons_of_ne he _ _, not_prefix_cons_of_ne (Ne.symm he) _ _,
      not_prefix_cons_of_ne he' _ _, not_prefix_cons_of_ne (Ne.symm he') _ _⟩
  · obtain ⟨c', hc⟩ := exists_ne c
    refine ⟨[a, c'], rfl, fun h => ?_, fun h => ?_, not_prefix_cons_of_ne (Ne.symm hab) _ _,
      not_prefix_cons_of_ne hab _ _⟩
    · exact not_prefix_cons_of_ne hc [] p2 (List.cons_prefix_cons.mp h).2
    · exact not_prefix_cons_of_ne (Ne.symm hc) p2 [] (List.cons_prefix_cons.mp h).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_exists_avoid2

theorem vgen_not_prefix_append_left {u w : List X} (c : List X) (h : ¬ u <+: w) :
    ¬ (u ++ c) <+: w :=
  fun h' => h ((List.prefix_append u c).trans h')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_not_prefix_append_left

theorem vgen_not_prefix_append_right {u w : List X} (c : List X) (h1 : ¬ u <+: w)
    (h2 : ¬ w <+: u) : ¬ w <+: (u ++ c) := by
  intro h'
  rcases List.prefix_or_prefix_of_prefix h' (List.prefix_append u c) with h | h
  · exact h2 h
  · exact h1 h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_not_prefix_append_right

/-- Incomparable words with a common prefix have incomparable tails, and conversely. -/
theorem vgen_not_prefix_append_swap {p u c c' : List X} (h : ¬ (p ++ c) <+: (p ++ c')) :
    ¬ (u ++ c) <+: (u ++ c') :=
  fun h' => h ((List.prefix_append_right_inj p).mpr ((List.prefix_append_right_inj u).mp h'))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_not_prefix_append_swap

end GroupApproximation.BooneHigman.Metabelian.Envelope
