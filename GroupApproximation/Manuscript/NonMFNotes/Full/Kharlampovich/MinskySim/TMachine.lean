import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.Minsky
import Mathlib.Logic.Function.Iterate

/-!
# Structured counter machines

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, via the
undecidability of the halting problem for Minsky machines (Minsky 1967;
Kharlampovich--Myasnikov--Sapir, arXiv:1204.6506, Sec. 3).

To build a deterministic Minsky machine simulating a modular machine we first
work with a *structured* machine.  It has an arbitrary finite state type `σ` and
a partial transition function `δ : σ → Option (TInstr K σ)`, so it is
deterministic by construction.  An instruction either adds one to a glass, or
tests a glass: if the glass is empty control goes to `jzero`, and otherwise the
glass loses one and control goes to `jpos`.

A machine reaches its stop configuration (stop state, all glasses empty) exactly
when some iterate of the total one-step map `next` hits it
(`reaches_stopc_iff`).  The lemma `iterate_stopc_of_iterate` is the bookkeeping
that lets halting be proved by strong induction on the length of the run.
-/

namespace GroupApproximation.Full.Kharlampovich.MinskySim

/-- A structured single-glass instruction over `K` glasses and states `σ`
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
inductive TInstr (K : ℕ) (σ : Type) : Type where
  /-- add one to glass `n`, go to `j` -/
  | add (n : Fin K) (j : σ)
  /-- if glass `n` is empty go to `jzero`, else take one from it and go to `jpos` -/
  | test (n : Fin K) (jpos jzero : σ)

namespace TInstr

variable {K : ℕ} {σ : Type}

/-- Executing an instruction on the glass contents
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def exec : TInstr K σ → (Fin K → ℕ) → σ × (Fin K → ℕ)
  | .add n j, g => (j, Function.update g n (g n + 1))
  | .test n jpos jzero, g =>
      if g n = 0 then (jzero, g) else (jpos, Function.update g n (g n - 1))

/-- Unfolding `exec` for `add` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem exec_add (n : Fin K) (j : σ) (g : Fin K → ℕ) :
    (TInstr.add n j).exec g = (j, Function.update g n (g n + 1)) := rfl

/-- Unfolding `exec` for `test` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem exec_test (n : Fin K) (jp jz : σ) (g : Fin K → ℕ) :
    (TInstr.test n jp jz).exec g =
      if g n = 0 then (jz, g) else (jp, Function.update g n (g n - 1)) := rfl

/-- A test on an empty glass (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem exec_test_zero (n : Fin K) (jp jz : σ) {g : Fin K → ℕ} (h : g n = 0) :
    (TInstr.test n jp jz).exec g = (jz, g) := by
  rw [exec_test, if_pos h]

/-- A test on a nonempty glass (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem exec_test_pos (n : Fin K) (jp jz : σ) {g : Fin K → ℕ} {x : ℕ} (h : g n = x + 1) :
    (TInstr.test n jp jz).exec g = (jp, Function.update g n x) := by
  have hne : g n ≠ 0 := by omega
  rw [exec_test, if_neg hne, h, Nat.add_sub_cancel]

end TInstr

/-- A structured counter machine: partial transition function with a
distinguished stop state that has no instruction
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
structure TMachine (K : ℕ) (σ : Type) : Type where
  /-- the instruction at each state, if any -/
  δ : σ → Option (TInstr K σ)
  /-- the stop state -/
  stop : σ
  /-- the stop state has no instruction -/
  δ_stop : δ stop = none

namespace TMachine

variable {K : ℕ} {σ : Type} (T : TMachine K σ)

/-- One step of a structured machine
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def step (c : σ × (Fin K → ℕ)) : Option (σ × (Fin K → ℕ)) :=
  (T.δ c.1).map fun i ↦ i.exec c.2

/-- The one-step relation (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
def StepRel (c d : σ × (Fin K → ℕ)) : Prop := T.step c = some d

/-- The total one-step map, fixing configurations without a step
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def next (c : σ × (Fin K → ℕ)) : σ × (Fin K → ℕ) := (T.step c).getD c

/-- The stop configuration (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
def stopc : σ × (Fin K → ℕ) := (T.stop, fun _ ↦ 0)

/-- A step at a state with an instruction (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem step_of_δ {a : σ} {i : TInstr K σ} (h : T.δ a = some i) (g : Fin K → ℕ) :
    T.step (a, g) = some (i.exec g) := by
  simp only [step, h, Option.map_some]

/-- No step at a state without an instruction (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem step_eq_none_of_δ {a : σ} (h : T.δ a = none) (g : Fin K → ℕ) :
    T.step (a, g) = none := by
  simp only [step, h, Option.map_none]

/-- `next` follows a step (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem next_of_step {c d : σ × (Fin K → ℕ)} (h : T.step c = some d) : T.next c = d := by
  simp only [next, h, Option.getD_some]

/-- `next` fixes a configuration without a step (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem next_of_step_none {c : σ × (Fin K → ℕ)} (h : T.step c = none) : T.next c = c := by
  simp only [next, h, Option.getD_none]

/-- The stop configuration has no step (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem step_stopc : T.step T.stopc = none :=
  T.step_eq_none_of_δ T.δ_stop (fun _ ↦ 0)

/-- `next` fixes the stop configuration (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem next_stopc : T.next T.stopc = T.stopc :=
  T.next_of_step_none T.step_stopc

/-- Iterates of `next` fix the stop configuration (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem iterate_next_stopc (n : ℕ) : T.next^[n] T.stopc = T.stopc :=
  Function.iterate_fixed T.next_stopc n

/-! ## Leading to a configuration -/

/-- `c` leads to `d` in some number of `next` steps (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def Leads (c d : σ × (Fin K → ℕ)) : Prop := ∃ k, T.next^[k] c = d

/-- `c` leads to `d` in a positive number of `next` steps (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
def Leads1 (c d : σ × (Fin K → ℕ)) : Prop := ∃ k, 0 < k ∧ T.next^[k] c = d

/-- Reflexivity of `Leads` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads_refl (c : σ × (Fin K → ℕ)) : T.Leads c c := ⟨0, rfl⟩

/-- Transitivity of `Leads` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads_trans {c d e : σ × (Fin K → ℕ)} (h1 : T.Leads c d) (h2 : T.Leads d e) :
    T.Leads c e := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by rw [Function.iterate_add_apply, hk1, hk2]⟩

/-- `Leads1` implies `Leads` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads_of_leads1 {c d : σ × (Fin K → ℕ)} (h : T.Leads1 c d) : T.Leads c d := by
  obtain ⟨k, _, hk⟩ := h
  exact ⟨k, hk⟩

/-- `Leads1` then `Leads` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads1_trans_leads {c d e : σ × (Fin K → ℕ)} (h1 : T.Leads1 c d)
    (h2 : T.Leads d e) : T.Leads1 c e := by
  obtain ⟨k1, hk1pos, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  exact ⟨k2 + k1, by omega, by rw [Function.iterate_add_apply, hk1, hk2]⟩

/-- `Leads` then `Leads1` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads_trans_leads1 {c d e : σ × (Fin K → ℕ)} (h1 : T.Leads c d)
    (h2 : T.Leads1 d e) : T.Leads1 c e := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2pos, hk2⟩ := h2
  exact ⟨k2 + k1, by omega, by rw [Function.iterate_add_apply, hk1, hk2]⟩

/-- One step gives `Leads1` (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads1_of_step {c d : σ × (Fin K → ℕ)} (h : T.step c = some d) : T.Leads1 c d :=
  ⟨1, Nat.zero_lt_one, T.next_of_step h⟩

/-- An `add` instruction (input for `thm:fixed-radical-membership`,
`non_mf_group_notes.tex`). -/
theorem leads1_add {a j : σ} {n : Fin K} (h : T.δ a = some (TInstr.add n j)) (g : Fin K → ℕ) :
    T.Leads1 (a, g) (j, Function.update g n (g n + 1)) := by
  apply T.leads1_of_step
  rw [T.step_of_δ h g, TInstr.exec_add]

/-- A `test` instruction on an empty glass (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem leads1_test_zero {a jp jz : σ} {n : Fin K} (h : T.δ a = some (TInstr.test n jp jz))
    {g : Fin K → ℕ} (hg : g n = 0) : T.Leads1 (a, g) (jz, g) := by
  apply T.leads1_of_step
  rw [T.step_of_δ h g, TInstr.exec_test_zero n jp jz hg]

/-- A `test` instruction on a nonempty glass (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem leads1_test_pos {a jp jz : σ} {n : Fin K} (h : T.δ a = some (TInstr.test n jp jz))
    {g : Fin K → ℕ} {x : ℕ} (hg : g n = x + 1) :
    T.Leads1 (a, g) (jp, Function.update g n x) := by
  apply T.leads1_of_step
  rw [T.step_of_δ h g, TInstr.exec_test_pos n jp jz hg]

/-! ## Reaching the stop configuration -/

/-- A run of steps gives an iterate of `next` (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem leads_of_reaches {c d : σ × (Fin K → ℕ)}
    (h : Relation.ReflTransGen T.StepRel c d) : T.Leads c d := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact T.leads_refl _
  | head hstep _ ih => exact T.leads_trans (T.leads_of_leads1 (T.leads1_of_step hstep)) ih

/-- An iterate of `next` hitting the stop configuration is a run of steps
(input for `thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem reaches_stopc_of_iterate (n : ℕ) :
    ∀ c, T.next^[n] c = T.stopc → Relation.ReflTransGen T.StepRel c T.stopc := by
  induction n with
  | zero =>
    intro c h
    have hc : c = T.stopc := h
    subst hc
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro c h
    have h' : T.next^[n] (T.next c) = T.stopc := h
    cases hs : T.step c with
    | none =>
      have hc : T.next c = c := T.next_of_step_none hs
      rw [hc] at h'
      exact ih c h'
    | some d =>
      have hc : T.next c = d := T.next_of_step hs
      rw [hc] at h'
      exact Relation.ReflTransGen.head (show T.StepRel c d from hs) (ih d h')

/-- Reaching the stop configuration, via iterates of `next` (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem reaches_stopc_iff (c : σ × (Fin K → ℕ)) :
    Relation.ReflTransGen T.StepRel c T.stopc ↔ ∃ n, T.next^[n] c = T.stopc :=
  ⟨T.leads_of_reaches, fun ⟨n, h⟩ ↦ T.reaches_stopc_of_iterate n c h⟩

/-- If `c` halts in `n` steps and leads in `k` steps to some other configuration
`d`, then `k ≤ n` and `d` halts in `n - k` steps (input for
`thm:fixed-radical-membership`, `non_mf_group_notes.tex`). -/
theorem iterate_stopc_of_iterate {c d : σ × (Fin K → ℕ)} {k n : ℕ}
    (hk : T.next^[k] c = d) (hd : d ≠ T.stopc) (hn : T.next^[n] c = T.stopc) :
    k ≤ n ∧ T.next^[n - k] d = T.stopc := by
  by_cases hkn : k ≤ n
  · refine ⟨hkn, ?_⟩
    rw [← hk, ← Function.iterate_add_apply, Nat.sub_add_cancel hkn, hn]
  · exfalso
    apply hd
    have hkn' : k = (k - n) + n := by omega
    rw [← hk, hkn', Function.iterate_add_apply, hn, T.iterate_next_stopc]

end TMachine

end GroupApproximation.Full.Kharlampovich.MinskySim
