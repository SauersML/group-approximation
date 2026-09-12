import GroupApproximation.Computability.PostMachine

/-!
# Cutting a machine down to the states it actually uses

`Computability.PostMachine` presents a machine by a finite list of rules, built
by `flatMap` over an enumeration of the state set.  That needs the state set to
be finite.  The machines that undecidability comes from are not like that:
Mathlib's `PartrecToTM2` machine has an *infinite* state type --- its states
carry continuations, which carry codes --- even though any single run visits
finitely many states.

So "infinitely many states, finitely many reachable" has to become "finitely
many states".  That is what this file does.  Given a `Finset` of states closed
under the transition function, `restrict` cuts the machine down to it; the
restricted machine has a `Fintype` state type, so the enumeration the rule list
wants exists.

The point is that nothing is lost: `step_restrict` says the two step functions
agree under the forgetful map, `step_restrict_eq_none_iff` says they halt
together, and `reach_iff` says the runs correspond in both directions.  The
backward direction needs no surjectivity --- it says a run downstairs starting
at an image *is* the image of a run upstairs, which is the same shape
`PostMachineTM0.reaches_iff` uses for the same reason.

The closure hypothesis is not needed to *define* the restriction: the definition
sends a transition leaving `S` to `none`, and closure is what says that branch
never fires.  Keeping it out of the definition means the definition is
computable and the hypothesis is only where it is used.
-/

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

variable {Γ Λ : Type} [DecidableEq Λ]

/-- The machine on a set of states.  A transition leaving `S` is turned into a
halt; under the closure hypothesis below, that never happens. -/
def restrict (M : Machine Γ Λ) (S : Finset Λ) : Machine Γ {q // q ∈ S} :=
  fun q a =>
    match M q.1 a with
    | none => none
    | some p => if h : p.1 ∈ S then some (⟨p.1, h⟩, p.2) else none

/-- `S` is closed under the transitions of `M`. -/
def Closed (M : Machine Γ Λ) (S : Finset Λ) : Prop :=
  ∀ q ∈ S, ∀ a : Γ, ∀ q' : Λ, ∀ act : Action Γ, M q a = some (q', act) → q' ∈ S

theorem restrict_eq_none {M : Machine Γ Λ} {S : Finset Λ} {q : {q // q ∈ S}} {a : Γ}
    (h : M q.1 a = none) : restrict M S q a = none := by
  simp [restrict, h]

theorem restrict_eq_some {M : Machine Γ Λ} {S : Finset Λ} {q : {q // q ∈ S}} {a : Γ}
    {q' : Λ} {act : Action Γ} (h : M q.1 a = some (q', act)) (hq' : q' ∈ S) :
    restrict M S q a = some (⟨q', hq'⟩, act) := by
  simp [restrict, h, hq']

/-- Forgetting that the state lies in `S`. -/
def unrestrictCfg {S : Finset Λ} (c : Cfg Γ {q // q ∈ S}) : Cfg Γ Λ :=
  ⟨c.q.1, c.left, c.head, c.right⟩

omit [DecidableEq Λ] in
omit [DecidableEq Λ] in
theorem unrestrictCfg_injective {S : Finset Λ} :
    Function.Injective (unrestrictCfg : Cfg Γ {q // q ∈ S} → Cfg Γ Λ) := by
  rintro ⟨q₁, l₁, h₁, r₁⟩ ⟨q₂, l₂, h₂, r₂⟩ h
  simp only [unrestrictCfg, Cfg.mk.injEq] at h
  obtain ⟨hq, hl, hh, hr⟩ := h
  simp only [Cfg.mk.injEq]
  exact ⟨Subtype.ext hq, hl, hh, hr⟩

variable [Inhabited Γ]

/-- **The two machines step together.**  Under the forgetful map, a step of the
restricted machine is a step of the original. -/
theorem step_restrict (M : Machine Γ Λ) {S : Finset Λ} (hS : Closed M S)
    (c : Cfg Γ {q // q ∈ S}) :
    (step (restrict M S) c).map unrestrictCfg = step M (unrestrictCfg c) := by
  unfold step
  cases hM : M c.q.1 c.head with
  | none =>
    rw [show (unrestrictCfg c).q = c.q.1 from rfl, show (unrestrictCfg c).head = c.head from rfl,
      hM, restrict_eq_none hM]
    simp
  | some p =>
    obtain ⟨q', act⟩ := p
    have hq' : q' ∈ S := hS c.q.1 c.q.2 c.head q' act hM
    rw [show (unrestrictCfg c).q = c.q.1 from rfl, show (unrestrictCfg c).head = c.head from rfl,
      hM, restrict_eq_some hM hq']
    cases act with
    | write b => simp [unrestrictCfg]
    | moveRight => cases hr : c.right <;> simp [unrestrictCfg, hr]
    | moveLeft => cases hl : c.left <;> simp [unrestrictCfg, hl]

/-- They halt together. -/
theorem step_restrict_eq_none_iff (M : Machine Γ Λ) {S : Finset Λ} (hS : Closed M S)
    (c : Cfg Γ {q // q ∈ S}) :
    step (restrict M S) c = none ↔ step M (unrestrictCfg c) = none := by
  rw [← step_restrict M hS c]
  simp

/-- A run of the restricted machine is a run of the original. -/
theorem reach_unrestrict {M : Machine Γ Λ} {S : Finset Λ} (hS : Closed M S)
    {c d : Cfg Γ {q // q ∈ S}} (h : Reach (step (restrict M S)) c d) :
    Reach (step M) (unrestrictCfg c) (unrestrictCfg d) := by
  induction h with
  | refl => exact Reach.refl _
  | tail _ hstep ih =>
    refine ih.tail ?_
    rw [← step_restrict M hS, hstep]
    simp

/-- **Runs correspond in both directions.**  A run of the original machine out
of a restricted configuration is the image of a run of the restricted one.  No
surjectivity is needed, and no injectivity either: the commuting square hands
back the configuration upstairs together with its step, which is exactly the
existential.  Injectivity is what upgrades this to `reach_iff_reach` below. -/
theorem reach_iff {M : Machine Γ Λ} {S : Finset Λ} (hS : Closed M S)
    {c : Cfg Γ {q // q ∈ S}} {X : Cfg Γ Λ} :
    Reach (step M) (unrestrictCfg c) X ↔
      ∃ d, Reach (step (restrict M S)) c d ∧ X = unrestrictCfg d := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨c, Reach.refl c, rfl⟩
    | tail _ hstep ih =>
      obtain ⟨d, hcd, rfl⟩ := ih
      rw [← step_restrict M hS] at hstep
      obtain ⟨e, he, hXe⟩ := Option.mem_map.mp hstep
      exact ⟨e, hcd.tail he, hXe.symm⟩
  · rintro ⟨d, hcd, rfl⟩
    exact reach_unrestrict hS hcd

/-- **The same, with a named endpoint.**  Here injectivity of `unrestrictCfg` is
what does the work: it identifies the configuration `reach_iff` produces with
the one that was asked about.  This is the form to use when both ends of the run
are already restricted configurations. -/
theorem reach_iff_reach {M : Machine Γ Λ} {S : Finset Λ} (hS : Closed M S)
    (c d : Cfg Γ {q // q ∈ S}) :
    Reach (step M) (unrestrictCfg c) (unrestrictCfg d) ↔
      Reach (step (restrict M S)) c d := by
  rw [reach_iff hS]
  constructor
  · rintro ⟨e, hce, he⟩
    obtain rfl := unrestrictCfg_injective he
    exact hce
  · intro h
    exact ⟨d, h, rfl⟩

/-! ## The payoff

The restricted state type is a `Fintype`, so the enumeration `machineRules`
wants exists.  It is an existence statement rather than a definition because
`Finset.toList` is noncomputable; a caller who needs the list computably should
pass one in, exactly as `PostMachine.machineRules` already asks. -/

omit [DecidableEq Λ] in
theorem exists_states_enumeration (S : Finset Λ) :
    ∃ l : List {q // q ∈ S}, ∀ q : {q // q ∈ S}, q ∈ l :=
  ⟨S.attach.toList, fun q => by simp⟩

/-- **The restricted machine is presented by a finite rewriting system.**  This
is what the whole file is for, and it is the step the unrestricted machine
cannot take: `presents_machineSystem` needs an enumeration of the states, the
original has none, and the restriction does.  The tape alphabet still has to be
enumerated by the caller, since nothing here makes `Γ` finite. -/
theorem exists_presents_machineSystem_restrict (M : Machine Γ Λ) (S : Finset Λ)
    {tapes : List Γ} (htapes : ∀ a : Γ, a ∈ tapes) :
    ∃ states : List {q // q ∈ S},
      Presents (restrict M S) (machineSystem (restrict M S) states tapes) := by
  obtain ⟨states, hstates⟩ := exists_states_enumeration S
  exact ⟨states, presents_machineSystem (restrict M S) hstates htapes⟩

end PostMachine
end StringRewriting
end GroupApproximation
