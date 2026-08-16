import GroupApproximation.Computability.PostMachine

/-!
# Restricting a machine to an invariant set of states

A machine with infinitely many states is useless to a *finite* presentation:
`machineRules` enumerates the rules by running over a list of states, and there
is no such list.  But a machine can have infinitely many states and still only
ever visit finitely many --- the standard construction of a universal machine
does exactly that, carrying continuations in its state --- and then the
infinitude is an artefact of how the state type was written down, not a
property of the machine.  This file removes the artefact.

If a set `S` of states is *invariant* (`Invariant`: no transition out of `S`
leaves `S`), the machine restricts to a machine on the subtype `{q // q ∈ S}`.
The restriction is not `Option.map`: the state it produces has to carry a proof
of membership, and that proof is available only from the *equation* saying which
transition fired, so the definition is a dependent match.

Everything else here says that nothing is lost by restricting.  `unrestrictCfg`
forgets the membership proof, and

* `map_unrestrictCfg_step` --- the square commutes: one step upstairs, then
  forget, is one step downstairs.  Every other statement is a corollary.
* `step_restrict_eq_none_iff` --- the restricted machine halts exactly where the
  original does.
* `reach_unrestrictCfg` and `reach_unrestrictCfg_iff` --- runs transfer both
  ways.  The backward direction is stated with an existential, `∃ d, … ∧
  X = unrestrictCfg d`, which is the shape a simulation argument consumes: a
  run downstairs out of an image is the image of a run upstairs.  Note that
  this needs *nothing* about injectivity --- only the commuting square, which
  hands back the configuration upstairs together with its step.  Injectivity of
  `unrestrictCfg` is a separate fact, and what it buys is the sharper
  `reach_unrestrictCfg_iff_reach`, where the endpoint is a named configuration
  rather than an existentially quantified one.

The payoff is `presents_machineSystem_restrict`.  When `{q // q ∈ S}` is a
`Fintype` --- which is the whole point: `S` is the finite set of states a run
actually visits --- `stateList` is the enumeration `machineRules` was missing,
so the restricted machine has an explicit finite rule list and presents a
finitely presented monoid.  No hypothesis here says the original machine's
state type is finite, and none says the halting problem is decidable or not;
this file is the transport step alone.
-/

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

variable {Γ Λ : Type}

/-! ## The restricted machine -/

/-- A set of states is *invariant* when no transition out of it leaves it.
Spelled out: for every state `q ∈ S` and symbol `a`, if the machine moves to
`q'`, then `q' ∈ S`.  This is exactly the hypothesis under which the transition
function restricts to the subtype. -/
def Invariant (M : Machine Γ Λ) (S : Set Λ) : Prop :=
  ∀ q a q' act, q ∈ S → M q a = some (q', act) → q' ∈ S

/-- The machine restricted to an invariant set of states.

`Option.map` cannot define this.  The value carries a state, the restricted
machine has to produce a state *together with a proof that it lies in `S`*, and
invariance supplies that proof only when applied to the equation naming the
transition that fired.  A dependent match keeps that equation in scope, which is
the one thing `Option.map` throws away. -/
def restrict (M : Machine Γ Λ) (S : Set Λ) (hS : Invariant M S) :
    Machine Γ {q // q ∈ S} :=
  fun q a =>
    match h : M q.1 a with
    | none => none
    | some (q', act) => some (⟨q', hS _ _ _ _ q.2 h⟩, act)

/-- **The restricted machine is a lift of the original.**  Forgetting the
membership proof from the restricted transition returns the original
transition, so the restriction changes nothing but the type of the states.
Every fact below is extracted from this one equation. -/
theorem map_restrict (M : Machine Γ Λ) (S : Set Λ) (hS : Invariant M S)
    (q : {q // q ∈ S}) (a : Γ) :
    (restrict M S hS q a).map (fun p => (p.1.1, p.2)) = M q.1 a := by
  unfold restrict
  split <;> rename_i h <;> simp [h]

/-- The restricted machine halts exactly where the original does. -/
theorem restrict_eq_none_iff (M : Machine Γ Λ) (S : Set Λ) (hS : Invariant M S)
    (q : {q // q ∈ S}) (a : Γ) :
    restrict M S hS q a = none ↔ M q.1 a = none := by
  rw [← map_restrict M S hS q a, Option.map_eq_none_iff]

/-! ## Configurations -/

/-- A configuration of the restricted machine, read as a configuration of the
original: forget the membership proof, keep the tape. -/
def unrestrictCfg {S : Set Λ} (c : Cfg Γ {q // q ∈ S}) : Cfg Γ Λ :=
  ⟨c.q.1, c.left, c.head, c.right⟩

/-- Forgetting the membership proof loses nothing: the proof was unique, being a
proof of a proposition. -/
theorem unrestrictCfg_injective {S : Set Λ} :
    Function.Injective (unrestrictCfg : Cfg Γ {q // q ∈ S} → Cfg Γ Λ) := by
  rintro ⟨⟨q, hq⟩, l, a, r⟩ ⟨⟨q', hq'⟩, l', a', r'⟩ h
  simp only [unrestrictCfg, Cfg.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

/-! ## The commuting square -/

/-- **One step upstairs is one step downstairs.**  This is the whole content of
the restriction: the two machines run in lockstep, and the only difference
between their configurations is a membership proof that no step inspects. -/
theorem map_unrestrictCfg_step (M : Machine Γ Λ) [Inhabited Γ] {S : Set Λ}
    (hS : Invariant M S) (c : Cfg Γ {q // q ∈ S}) :
    (step (restrict M S hS) c).map unrestrictCfg = step M (unrestrictCfg c) := by
  have hmap := map_restrict M S hS c.q c.head
  cases hr : restrict M S hS c.q c.head with
  | none =>
    rw [hr] at hmap
    have h2 : M c.q.1 c.head = none := by simpa using hmap.symm
    rw [(step_eq_none_iff c).2 hr, (step_eq_none_iff (unrestrictCfg c)).2 h2]
    rfl
  | some p =>
    obtain ⟨Q, act⟩ := p
    rw [hr] at hmap
    have h2 : M c.q.1 c.head = some (Q.1, act) := by simpa using hmap.symm
    simp only [step, unrestrictCfg, hr, h2]
    cases act <;> cases c.left <;> cases c.right <;> rfl

/-- **Halting agrees.**  Immediate from the square, since `Option.map` sends
`none` to `none` and nothing else. -/
theorem step_restrict_eq_none_iff (M : Machine Γ Λ) [Inhabited Γ] {S : Set Λ}
    (hS : Invariant M S) (c : Cfg Γ {q // q ∈ S}) :
    step (restrict M S hS) c = none ↔ step M (unrestrictCfg c) = none := by
  rw [← map_unrestrictCfg_step M hS c, Option.map_eq_none_iff]

/-! ## Runs -/

/-- **Runs transfer downwards.**  A run of the restricted machine is a run of
the original between the corresponding configurations. -/
theorem reach_unrestrictCfg (M : Machine Γ Λ) [Inhabited Γ] {S : Set Λ}
    (hS : Invariant M S) {c d : Cfg Γ {q // q ∈ S}}
    (h : Reach (step (restrict M S hS)) c d) :
    Reach (step M) (unrestrictCfg c) (unrestrictCfg d) := by
  induction h with
  | refl => exact Reach.refl _
  | tail _ hstep ih =>
    refine ih.tail ?_
    rw [← map_unrestrictCfg_step M hS, hstep]
    rfl

/-- **Runs transfer upwards**, in the form the induction actually proves: the
starting configuration is generalised, because it is an index of `Reach` and
abstracting it while remembering that it is an image is exactly what the
equation hypothesis does. -/
theorem exists_reach_of_reach_unrestrictCfg (M : Machine Γ Λ) [Inhabited Γ]
    {S : Set Λ} (hS : Invariant M S) {Y X : Cfg Γ Λ} (h : Reach (step M) Y X) :
    ∀ c : Cfg Γ {q // q ∈ S}, Y = unrestrictCfg c →
      ∃ d, Reach (step (restrict M S hS)) c d ∧ X = unrestrictCfg d := by
  induction h with
  | refl => exact fun c hc => ⟨c, Reach.refl c, hc.symm⟩
  | tail _ hstep ih =>
    intro c hc
    obtain ⟨d, hcd, rfl⟩ := ih c hc
    rw [← map_unrestrictCfg_step M hS] at hstep
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hstep
    exact ⟨e, hcd.tail he, rfl⟩

/-- **Runs out of an image are exactly the images of runs.**  Both directions,
and the endpoint downstairs is produced rather than assumed to be an image ---
which is what makes this usable as a simulation statement.  Only the commuting
square is used; `unrestrictCfg` being injective plays no part. -/
theorem reach_unrestrictCfg_iff (M : Machine Γ Λ) [Inhabited Γ] {S : Set Λ}
    (hS : Invariant M S) (c : Cfg Γ {q // q ∈ S}) (X : Cfg Γ Λ) :
    Reach (step M) (unrestrictCfg c) X ↔
      ∃ d, Reach (step (restrict M S hS)) c d ∧ X = unrestrictCfg d := by
  constructor
  · intro h
    exact exists_reach_of_reach_unrestrictCfg M hS h c rfl
  · rintro ⟨d, hcd, rfl⟩
    exact reach_unrestrictCfg M hS hcd

/-- The same statement with a named endpoint.  *This* is where injectivity of
`unrestrictCfg` is needed: it turns the configuration the previous theorem
produces into the one that was asked about. -/
theorem reach_unrestrictCfg_iff_reach (M : Machine Γ Λ) [Inhabited Γ] {S : Set Λ}
    (hS : Invariant M S) (c d : Cfg Γ {q // q ∈ S}) :
    Reach (step M) (unrestrictCfg c) (unrestrictCfg d) ↔
      Reach (step (restrict M S hS)) c d := by
  rw [reach_unrestrictCfg_iff]
  constructor
  · rintro ⟨e, hce, he⟩
    obtain rfl := unrestrictCfg_injective he
    exact hce
  · intro h
    exact ⟨d, h, rfl⟩

/-! ## The payoff: a finite rule list -/

/-- The states of the restricted machine, as a list.  This is what the original
machine could not supply and the restriction can: `machineRules` enumerates the
rules by running over a list of states, and a `Fintype` instance on the subtype
is exactly such a list. -/
def stateList (S : Set Λ) [Fintype {q // q ∈ S}] : List {q // q ∈ S} :=
  (Finset.univ : Finset {q // q ∈ S}).toList

/-- Every restricted state is in the enumeration. -/
theorem mem_stateList {S : Set Λ} [Fintype {q // q ∈ S}] (q : {q // q ∈ S}) :
    q ∈ stateList S := by
  simp [stateList]

/-- **The restricted machine has an explicit finite rule list.**  Over a finite
invariant state set and a finite tape alphabet, `machineSystem` built from
`stateList` presents the restricted machine --- the hypothesis
`presents_machineSystem` wants about the state enumeration is `mem_stateList`,
and there was no way to supply it for the unrestricted machine. -/
theorem presents_machineSystem_restrict (M : Machine Γ Λ) [Inhabited Γ]
    (S : Set Λ) (hS : Invariant M S) [Fintype {q // q ∈ S}]
    {tapes : List Γ} (htapes : ∀ a : Γ, a ∈ tapes) :
    Presents (restrict M S hS)
      (machineSystem (restrict M S hS) (stateList S) tapes) :=
  presents_machineSystem (restrict M S hS) mem_stateList htapes

end PostMachine
end StringRewriting
end GroupApproximation
