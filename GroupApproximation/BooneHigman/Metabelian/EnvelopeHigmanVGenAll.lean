import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVGenInduct
import GroupApproximation.Meta.AxiomGuard

/-!
# All cone swaps from the short ones

`vgen_swapIn_of_short`: over an alphabet with at least two letters, a subgroup of
`Equiv.Perm (Cantor X)` containing the cone swaps of incomparable words of length `≤ 3` contains
every cone swap.  The inductive step is `vgen_step`; see `EnvelopeHigmanVGenInduct.lean`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*} [Nontrivial X] {G : Subgroup (Equiv.Perm (Cantor X))}

theorem vgen_step {n : ℕ} (hn : 3 ≤ n)
    (ih : ∀ v w : List X, v.length ≤ n → w.length ≤ n → VGenSwapIn G v w) :
    ∀ v w : List X, v.length ≤ n + 1 → w.length ≤ n + 1 → VGenSwapIn G v w := by
  intro v w hv hw
  rcases Nat.lt_or_ge w.length (n + 1) with hlt | hge
  · exact vgen_step_left hn ih hv (by omega)
  rcases Nat.lt_or_ge v.length (n + 1) with hlt' | hge'
  · exact vgen_step_right hn ih (by omega) hw
  obtain ⟨p, x, rfl, hp⟩ := vgen_split_last (le_antisymm hv hge')
  obtain ⟨q, z, rfl, hq⟩ := vgen_split_last (le_antisymm hw hge)
  by_cases hpq : p = q
  · rw [← hpq]
    have hp0 : p ≠ [] := List.ne_nil_of_length_pos (by omega)
    obtain ⟨u, hu, hup, hpu⟩ := vgen_exists_avoid1 hp0
    have hux : (u ++ [x]).length ≤ n := by
      simp only [List.length_append, List.length_singleton, hu]
      omega
    have huz : (u ++ [z]).length ≤ n := by
      simp only [List.length_append, List.length_singleton, hu]
      omega
    exact vgen_shorten_both x z hpu hup (ih p u (by omega) (by omega))
      (ih (u ++ [x]) (u ++ [z]) hux huz)
  · intro hvw hwv
    have hpw : ¬ p <+: q ++ [z] := by
      intro h
      rcases List.prefix_concat_iff.mp h with h' | h'
      · have hl := congrArg List.length h'
        simp only [List.length_append, List.length_singleton] at hl
        omega
      · exact hpq (h'.eq_of_length (by omega))
    have hwp : ¬ (q ++ [z]) <+: p := by
      intro h
      have hl := h.length_le
      simp only [List.length_append, List.length_singleton] at hl
      omega
    obtain ⟨u, hu, hup, hpu, huw, hwu⟩ := vgen_exists_avoid2 (by omega : 2 ≤ p.length) hwp
    exact vgen_shorten_left x hpu hup hpw hwp huw hwu (ih p u (by omega) (by omega))
      (vgen_step_right hn ih (by simp only [List.length_append, List.length_singleton, hu]; omega)
        hw) hvw hwv

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_step

theorem vgen_all (hbase : ∀ v w : List X, v.length ≤ 3 → w.length ≤ 3 → VGenSwapIn G v w) :
    ∀ (n : ℕ) (v w : List X), v.length ≤ n → w.length ≤ n → VGenSwapIn G v w := by
  intro n
  induction n with
  | zero =>
    intro v w hv hw
    exact hbase v w (by omega) (by omega)
  | succ n ih =>
    intro v w hv hw
    by_cases hn : 3 ≤ n
    · exact vgen_step hn ih v w hv hw
    · exact hbase v w (by omega) (by omega)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_all

/-- **Every cone swap from the short cone swaps.** -/
theorem vgen_swapIn_of_short
    (hbase : ∀ v w : List X, v.length ≤ 3 → w.length ≤ 3 → VGenSwapIn G v w) (v w : List X) :
    VGenSwapIn G v w :=
  vgen_all hbase (max v.length w.length) v w (le_max_left _ _) (le_max_right _ _)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.vgen_swapIn_of_short

end GroupApproximation.BooneHigman.Metabelian.Envelope
