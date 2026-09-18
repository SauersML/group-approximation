import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.MinskySim.TMachine
import GroupApproximation.Computability.BooneGroupModularMachine

/-!
# Simulating a modular machine by a structured Minsky machine

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  An
encoding `C` of modular-machine configurations into configurations of a
structured machine `T` is a *simulation* when:

* no encoded configuration is the stop configuration of `T`,
* every modular step is followed by at least one step of `T` between the codes,
* a stuck modular configuration other than `(0, 0)` leads `T` into a loop that
  never stops, and
* the code of `(0, 0)` leads `T` to the stop configuration.

For such an encoding, `(α, β)` halts exactly when `T` stops from its code
(`Simulates.halts_iff`).
-/

namespace GroupApproximation.Full.Kharlampovich.MinskySim

open GroupApproximation.BooneGroup

variable {K : ℕ} {σ : Type}

/-- The simulation conditions for an encoding `C` of the modular machine `mm`
into the structured machine `T` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
structure Simulates (mm : ModularMachine) (T : TMachine K σ)
    (C : ℕ × ℕ → σ × (Fin K → ℕ)) : Prop where
  /-- Codes are never the stop configuration. -/
  ne_stopc : ∀ p, C p ≠ T.stopc
  /-- A modular step is simulated by at least one step. -/
  step_some : ∀ p q, mm.step p = some q → T.Leads1 (C p) (C q)
  /-- A stuck nonzero configuration leads to a non-stop fixed point. -/
  step_none : ∀ p, p ≠ (0, 0) → mm.step p = none →
    ∃ d, T.Leads (C p) d ∧ T.next d = d ∧ d ≠ T.stopc
  /-- The code of `(0, 0)` leads to the stop configuration. -/
  halt : T.Leads (C (0, 0)) T.stopc

namespace Simulates

variable {mm : ModularMachine} {T : TMachine K σ} {C : ℕ × ℕ → σ × (Fin K → ℕ)}

/-- One inductive step of the backward direction (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem halts_of_iterate_aux (hS : Simulates mm T C) {n : ℕ} (p : ℕ × ℕ)
    (hn : T.next^[n] (C p) = T.stopc)
    (ih : ∀ m, m < n → ∀ q, T.next^[m] (C q) = T.stopc → mm.Halts q) : mm.Halts p := by
  by_cases hp : p = (0, 0)
  · subst hp
    exact mm.halts_zero_zero
  · cases hs : mm.step p with
    | none =>
      exfalso
      obtain ⟨d, ⟨k, hk⟩, hfix, hne⟩ := hS.step_none p hp hs
      obtain ⟨_, hd⟩ := T.iterate_stopc_of_iterate hk hne hn
      rw [Function.iterate_fixed hfix] at hd
      exact hne hd
    | some q =>
      obtain ⟨k, hkpos, hk⟩ := hS.step_some p q hs
      obtain ⟨hkn, hq⟩ := T.iterate_stopc_of_iterate hk (hS.ne_stopc q) hn
      have hlt : n - k < n := by omega
      have hq' : Relation.ReflTransGen mm.StepRel q (0, 0) := ih (n - k) hlt q hq
      have hpq : mm.StepRel p q := hs
      show Relation.ReflTransGen mm.StepRel p (0, 0)
      exact Relation.ReflTransGen.head hpq hq'

/-- Backward direction: if `T` stops from the code of `p`, then `p` halts
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem halts_of_iterate (hS : Simulates mm T C) (n : ℕ) :
    ∀ p : ℕ × ℕ, T.next^[n] (C p) = T.stopc → mm.Halts p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p hn
    exact hS.halts_of_iterate_aux p hn ih

/-- Forward direction: if `p` halts, then `T` stops from the code of `p`
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem iterate_of_halts (hS : Simulates mm T C) {p : ℕ × ℕ} (h : mm.Halts p) :
    ∃ n, T.next^[n] (C p) = T.stopc := by
  have h' : Relation.ReflTransGen mm.StepRel p (0, 0) := h
  clear h
  induction h' using Relation.ReflTransGen.head_induction_on with
  | refl => exact hS.halt
  | head hstep _ ih =>
    obtain ⟨k, _, hk⟩ := hS.step_some _ _ hstep
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + k, by rw [Function.iterate_add_apply, hk, hn]⟩

/-- A simulation reduces halting of the modular machine to stopping of `T`
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem halts_iff (hS : Simulates mm T C) (p : ℕ × ℕ) :
    mm.Halts p ↔ ∃ n, T.next^[n] (C p) = T.stopc :=
  ⟨hS.iterate_of_halts, fun ⟨n, hn⟩ ↦ hS.halts_of_iterate n p hn⟩

end Simulates

end GroupApproximation.Full.Kharlampovich.MinskySim
