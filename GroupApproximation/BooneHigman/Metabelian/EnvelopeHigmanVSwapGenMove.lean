import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVSwapGenLeaf
import GroupApproximation.Meta.AxiomGuard

/-!
# Shortening the longest targets by one cone swap

Let `f` be a prefix substitution of depth `N` whose targets have length `≤ N + B + 1`, let `q' ++ [x]`
be a target of maximal length `N + B + 1`, and let `p` be a target of length `< N`.  Then `p` and
`q'` are incomparable (`swapGen_move_incomparable`), and composing with `coneSwap p q'` turns
every target either into a word of length `≤ N + B`, or leaves it unchanged when it does not
extend `q'` (`swapGen_move`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- A short target and the parent of a longest target are incomparable. -/
theorem swapGen_move_incomparable [Nontrivial X] {f : Equiv.Perm (Cantor X)} {N B : ℕ}
    {wp p q' w₀ : List X} {x : X}
    (hp : MapsCone f wp p) (hpN : p.length < N) (hwp : wp.length = N)
    (hq : MapsCone f w₀ (q' ++ [x])) (hw₀ : w₀.length = N) (hq'N : q'.length = N + B) :
    ¬ p <+: q' ∧ ¬ q' <+: p := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hwu : wp = w₀ :=
      swapGen_source_eq_of_prefix hp hq (by rw [hwp, hw₀]) (List.prefix_append_of_prefix h)
    rw [hwu] at hp
    have hl := congrArg List.length (MapsCone.unique hp hq)
    rw [List.length_append, List.length_singleton] at hl
    omega
  · have hl := h.length_le
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_move_incomparable

/-- **The move.** After composing with `coneSwap p q'`, the target of a word of length `N` either
has length `≤ N + B`, or is unchanged and does not extend `q'`. -/
theorem swapGen_move [Nontrivial X] {f : Equiv.Perm (Cantor X)} {N B : ℕ}
    {wp p q' w₀ : List X} {x : X}
    (hp : MapsCone f wp p) (hpN : p.length < N) (hwp : wp.length = N)
    (hq : MapsCone f w₀ (q' ++ [x])) (hw₀ : w₀.length = N) (hq'N : q'.length = N + B)
    (hpq : ¬ p <+: q') (hqp : ¬ q' <+: p)
    {u t : List X} (hu : u.length = N) (ht : MapsCone f u t) (htN : t.length ≤ N + B + 1) :
    ∃ t', MapsCone (coneSwap p q' hpq hqp * f) u t' ∧
      (t'.length ≤ N + B ∨ (t' = t ∧ ¬ q' <+: t)) := by
  by_cases hpt : p <+: t
  · have hwu : wp = u := swapGen_source_eq_of_prefix hp ht (by rw [hwp, hu]) hpt
    rw [hwu] at hp
    have htp : p = t := MapsCone.unique hp ht
    rw [← htp] at ht
    exact ⟨q', MapsCone.comp ht (mapsCone_coneSwap_left hpq hqp), Or.inl (by omega)⟩
  by_cases hqt : q' <+: t
  · obtain ⟨s, rfl⟩ := hqt
    refine ⟨p ++ s, MapsCone.comp ht ((mapsCone_coneSwap_right hpq hqp).append s), Or.inl ?_⟩
    rw [List.length_append] at htN ⊢
    omega
  have htp : ¬ t <+: p := fun h => hpt (by
    have hwu : u = wp := swapGen_source_eq_of_prefix ht hp (by rw [hwp, hu]) h
    rw [hwu] at ht
    exact ⟨[], by rw [List.append_nil]; exact MapsCone.unique hp ht⟩)
  have htq : ¬ t <+: q' := fun h => by
    have hwu : u = w₀ :=
      swapGen_source_eq_of_prefix ht hq (by rw [hw₀, hu]) (List.prefix_append_of_prefix h)
    rw [hwu] at ht
    have hl := congrArg List.length (MapsCone.unique hq ht)
    rw [List.length_append, List.length_singleton] at hl
    have hl' := h.length_le
    omega
  exact ⟨t, MapsCone.comp ht (vgen_mapsCone_coneSwap_fix hpq hqp htp hpt htq hqt),
    Or.inr ⟨rfl, hqt⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.swapGen_move

end GroupApproximation.BooneHigman.Metabelian.Envelope
