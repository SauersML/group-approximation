import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic

/-!
# Minsky machines with single-glass commands

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`.  That
theorem uses Kharlampovich's finitely presented solvable group with undecidable
word problem.  We follow the account in Kharlampovich--Myasnikov--Sapir,
*Algorithmically complex residually finite groups* (arXiv:1204.6506), Sec. 3
"Minsky machines" and Sec. 4 "Simulation of Minsky machines in solvable groups".

Here a command touches a single glass:

* `i → Add(n); j`,
* `i, ε_n > 0 → Sub(n); j`,
* `i, ε_n = 0 → j`,

and command number `0` is the stop command, so no instruction starts in state
`0`.  Multi-glass commands of the source are compositions of these.

The configuration equivalence `≡_M` of the source is the equivalence closure of
the one-step relation.  The source's group-theoretic argument compares
configurations modulo `≡_M`, while undecidability concerns reachability.  The
bridge is the *symmetric computation lemma* (`l:sym` of the source): for a
deterministic machine a configuration is `≡_M`-equivalent to a terminal
configuration exactly when it reaches it.  This is proved here in general
(`reflTransGen_of_eqvGen_terminal`) and for machines
(`Machine.equiv_stopCfg_iff_reaches`).

Note on the source.  The semigroup `S(M)` of KMS Sec. 3 contains the stop
relation `q_0 = 0`, but the group relations G1--G8 have no counterpart.  So the
statement to prove on the group side is "config words are equal iff the
configurations are `≡_M`-equivalent", with no zero.
-/

namespace GroupApproximation.Full.Kharlampovich

/-! ## Deterministic relations -/

section Deterministic

variable {α : Type*} {r : α → α → Prop}

/-- Two computations of a deterministic relation from the same point are
comparable. -/
theorem reflTransGen_comparable (hdet : ∀ a b₁ b₂, r a b₁ → r a b₂ → b₁ = b₂)
    {a b : α} (hab : Relation.ReflTransGen r a b) :
    ∀ c, Relation.ReflTransGen r a c →
      Relation.ReflTransGen r b c ∨ Relation.ReflTransGen r c b := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro c hac
    exact Or.inl hac
  | head hstep hrest ih =>
    intro c hac
    rcases Relation.ReflTransGen.cases_head hac with hEq | ⟨e, hae, hec⟩
    · rw [← hEq]
      exact Or.inr (Relation.ReflTransGen.head hstep hrest)
    · have hce := hdet _ _ _ hstep hae
      rw [← hce] at hec
      exact ih _ hec

/-- For a deterministic relation, equivalent points have a common descendant. -/
theorem eqvGen_joinable (hdet : ∀ a b₁ b₂, r a b₁ → r a b₂ → b₁ = b₂) {a b : α}
    (h : Relation.EqvGen r a b) :
    ∃ e, Relation.ReflTransGen r a e ∧ Relation.ReflTransGen r b e := by
  induction h with
  | rel _ y hxy => exact ⟨y, Relation.ReflTransGen.single hxy, Relation.ReflTransGen.refl⟩
  | refl x => exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | symm _ _ _ ih =>
    obtain ⟨e, hxe, hye⟩ := ih
    exact ⟨e, hye, hxe⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨e₁, hxe₁, hye₁⟩ := ih₁
    obtain ⟨e₂, hye₂, hze₂⟩ := ih₂
    rcases reflTransGen_comparable hdet hye₁ e₂ hye₂ with h12 | h21
    · exact ⟨e₂, hxe₁.trans h12, hze₂⟩
    · exact ⟨e₁, hxe₁, hze₂.trans h21⟩

/-- **Symmetric computation lemma** (KMS `l:sym`, deterministic case).  A point
equivalent to a terminal point reaches it. -/
theorem reflTransGen_of_eqvGen_terminal (hdet : ∀ a b₁ b₂, r a b₁ → r a b₂ → b₁ = b₂)
    {a b : α} (h : Relation.EqvGen r a b) (hb : ∀ c, ¬ r b c) :
    Relation.ReflTransGen r a b := by
  obtain ⟨e, hae, hbe⟩ := eqvGen_joinable hdet h
  rcases Relation.ReflTransGen.cases_head hbe with hEq | ⟨c, hbc, _⟩
  · rw [hEq]
    exact hae
  · exact absurd hbc (hb c)

/-- Reachability implies equivalence. -/
theorem eqvGen_of_reflTransGen {a b : α} (h : Relation.ReflTransGen r a b) :
    Relation.EqvGen r a b := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | tail _ hbc ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)

end Deterministic

namespace Minsky

/-- A single-glass Minsky instruction on `K` glasses, with target command number
in `Fin (N + 1)` (KMS Sec. 3). -/
inductive Instr (K N : ℕ) : Type where
  /-- `i → Add(n); j`. -/
  | add (n : Fin K) (j : Fin (N + 1)) : Instr K N
  /-- `i, ε_n > 0 → Sub(n); j`. -/
  | sub (n : Fin K) (j : Fin (N + 1)) : Instr K N
  /-- `i, ε_n = 0 → j`. -/
  | zero (n : Fin K) (j : Fin (N + 1)) : Instr K N

/-- A configuration `(i; ε_1, …, ε_K)`. -/
structure Cfg (K N : ℕ) : Type where
  /-- The number of the command to be executed. -/
  state : Fin (N + 1)
  /-- The number of coins in each glass. -/
  glass : Fin K → ℕ

/-- A Minsky machine: a finite list of numbered instructions.  Command `0` is the
stop command, so no instruction is numbered `0`. -/
structure Machine (K N : ℕ) : Type where
  /-- The numbered instructions. -/
  prog : List (Fin (N + 1) × Instr K N)
  /-- No instruction starts at the stop command. -/
  stop_terminal : ∀ r ∈ prog, r.1 ≠ 0

variable {K N : ℕ}

/-- When an instruction takes configuration `c` to configuration `d`.  The source
state is checked separately, in `Machine.Step`. -/
def Instr.Fires : Instr K N → Cfg K N → Cfg K N → Prop
  | .add n j, c, d => d.state = j ∧ d.glass = Function.update c.glass n (c.glass n + 1)
  | .sub n j, c, d =>
      0 < c.glass n ∧ d.state = j ∧ d.glass = Function.update c.glass n (c.glass n - 1)
  | .zero n j, c, d => c.glass n = 0 ∧ d.state = j ∧ d.glass = c.glass

/-- The stop configuration `(0; 0, …, 0)`. -/
def stopCfg (K N : ℕ) : Cfg K N := ⟨0, fun _ ↦ 0⟩

/-- The glass contents `(α, β, 0, …, 0)`, which is the input format used for
simulating a modular machine. -/
def initGlasses (K : ℕ) (a b : ℕ) : Fin K → ℕ :=
  fun n ↦ if n.val = 0 then a else if n.val = 1 then b else 0

namespace Machine

variable (M : Machine K N)

/-- One step of the machine. -/
def Step (c d : Cfg K N) : Prop :=
  ∃ r ∈ M.prog, r.1 = c.state ∧ r.2.Fires c d

/-- Reachability `c →* d`. -/
def Reaches : Cfg K N → Cfg K N → Prop :=
  Relation.ReflTransGen M.Step

/-- The configuration equivalence `≡_M` of KMS Sec. 3: the equivalence closure of
one step. -/
def Equiv : Cfg K N → Cfg K N → Prop :=
  Relation.EqvGen M.Step

/-- Determinism: at most one successor for every configuration. -/
def Deterministic : Prop :=
  ∀ c d₁ d₂, M.Step c d₁ → M.Step c d₂ → d₁ = d₂

/-- Configurations at the stop command have no successor. -/
theorem not_step_of_state_eq_zero {c d : Cfg K N} (hc : c.state = 0) : ¬ M.Step c d := by
  rintro ⟨r, hr, hrs, _⟩
  exact M.stop_terminal r hr (hrs.trans hc)

theorem not_step_stopCfg (d : Cfg K N) : ¬ M.Step (stopCfg K N) d :=
  M.not_step_of_state_eq_zero rfl

theorem equiv_of_reaches {c d : Cfg K N} (h : M.Reaches c d) : M.Equiv c d :=
  eqvGen_of_reflTransGen (r := M.Step) h

/-- **Symmetric computation lemma for Minsky machines** (KMS `l:sym`,
deterministic case): a configuration is `≡_M`-equivalent to the stop
configuration exactly when the machine takes it there. -/
theorem equiv_stopCfg_iff_reaches (hM : M.Deterministic) (c : Cfg K N) :
    M.Equiv c (stopCfg K N) ↔ M.Reaches c (stopCfg K N) :=
  ⟨fun h ↦ reflTransGen_of_eqvGen_terminal (r := M.Step) hM h M.not_step_stopCfg,
    M.equiv_of_reaches⟩

end Machine

end Minsky

end GroupApproximation.Full.Kharlampovich
