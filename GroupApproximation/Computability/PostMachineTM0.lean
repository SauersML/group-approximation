import GroupApproximation.Computability.PostMachine
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# The simulated machine is Mathlib's Post--Turing machine

`Computability.PostMachine` simulates a machine of its own by a finite rewriting
system.  That is only worth having if the machine is the one the rest of the
world computes with, so this file identifies it with `Turing.TM0`.

The transition types agree on the nose: `Turing.TM0.Machine Γ Λ` is
`Λ → Γ → Option (Λ × TM0.Stmt Γ)` and `PostMachine.Machine Γ Λ` is
`Λ → Γ → Option (Λ × Action Γ)`, with `TM0.Stmt` and `Action` the same three
commands.  What has to be checked is the *tape*.  Mathlib's tape is a pair of
`Turing.ListBlank`s --- lists quotiented by trailing blanks --- while a `Cfg`
here carries raw lists and materialises a blank whenever a move leaves the
written portion.  Those are the same machine: `ListBlank.head` of the empty list
is `default`, and its `tail` is again empty, which is exactly the
blank-on-demand clause of `PostMachine.step`.

`toTM0_step` is that statement, and everything else follows from it.

## What this does not give, and why

`toTM0` is *not* injective: `[a]` and `[a, default]` are different `Cfg` tapes
but the same `ListBlank`.  So a TM0 run cannot be pulled back to a *named*
`Cfg`; what `reaches_iff` gives instead is that TM0 runs out of `toTM0 c` are
exactly the images of runs out of `c`.  That is enough to transport halting and
reachability, and it is the honest statement --- pinning down a unique `Cfg`
needs canonical representatives (lists with no trailing blank), which is a
separate matter.
-/

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

open Turing

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ]

/-- A TM0 statement, read as an action.  The two types carry the same three
commands. -/
def ofStmt : TM0.Stmt Γ → Action Γ
  | .write b => .write b
  | .move Dir.left => .moveLeft
  | .move Dir.right => .moveRight

/-- Mathlib's Post--Turing machine, read as a machine here. -/
def ofTM0 (M : TM0.Machine Γ Λ) : Machine Γ Λ :=
  fun q a => (M q a).map fun p => (p.1, ofStmt p.2)

/-- A configuration, read as a TM0 configuration.  The written tape becomes a
`ListBlank`; everything past it is blank in both readings. -/
def toTM0 (c : Cfg Γ Λ) : TM0.Cfg Γ Λ :=
  ⟨c.q, ⟨c.head, ListBlank.mk c.left, ListBlank.mk c.right⟩⟩

/-- Halting agrees: both machines stop exactly where the transition function
returns `none`. -/
@[simp] theorem step_ofTM0_eq_none_iff (M : TM0.Machine Γ Λ) (c : Cfg Γ Λ) :
    step (ofTM0 M) c = none ↔ M c.q c.head = none := by
  unfold step ofTM0
  cases M c.q c.head with
  | none => simp
  | some p =>
    obtain ⟨q', stmt⟩ := p
    cases stmt with
    | write b => simp [ofStmt]
    | move d => cases d <;> cases c.left <;> cases c.right <;> simp [ofStmt]

/-- **The step functions agree.**  This is the whole content of the file: a
blank materialised at the end of a written list is the same thing as the head of
an empty `ListBlank`. -/
theorem toTM0_step (M : TM0.Machine Γ Λ) (c : Cfg Γ Λ) :
    (step (ofTM0 M) c).map toTM0 = TM0.step M (toTM0 c) := by
  unfold step ofTM0 toTM0 TM0.step
  cases hM : M c.q c.head with
  | none => simp [hM]
  | some p =>
    obtain ⟨q', stmt⟩ := p
    cases stmt with
    | write b => simp [hM, ofStmt, Tape.write]
    | move d =>
      cases d with
      | left =>
        cases hl : c.left with
        | nil => simp [hM, ofStmt, Tape.move]
        | cons y l => simp [hM, ofStmt, Tape.move]
      | right =>
        cases hr : c.right with
        | nil => simp [hM, ofStmt, Tape.move]
        | cons x r => simp [hM, ofStmt, Tape.move]

/-- A run here gives a TM0 run. -/
theorem reaches_toTM0 {M : TM0.Machine Γ Λ} {c d : Cfg Γ Λ}
    (h : Reach (step (ofTM0 M)) c d) : TM0.Reaches M (toTM0 c) (toTM0 d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    refine ih.tail ?_
    rw [← toTM0_step, hstep]
    simp

/-- **TM0 runs out of an encoded configuration are exactly the encoded runs.**
Stated this way because `toTM0` is not injective, so a TM0 configuration does
not name a `Cfg`; what is true is that it is *some* `Cfg` reachable here. -/
theorem reaches_iff {M : TM0.Machine Γ Λ} {c : Cfg Γ Λ} {X : TM0.Cfg Γ Λ} :
    TM0.Reaches M (toTM0 c) X ↔ ∃ e, Reach (step (ofTM0 M)) c e ∧ X = toTM0 e := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨c, Reach.refl c, rfl⟩
    | tail _ hstep ih =>
      obtain ⟨e, hce, rfl⟩ := ih
      rw [← toTM0_step] at hstep
      obtain ⟨f, hf, hXf⟩ := Option.mem_map.mp hstep
      exact ⟨f, hce.tail hf, hXf.symm⟩
  · rintro ⟨e, hce, rfl⟩
    exact reaches_toTM0 hce

/-- A halting configuration here is a halting TM0 configuration. -/
theorem tm0_step_eq_none {M : TM0.Machine Γ Λ} {c : Cfg Γ Λ}
    (hc : step (ofTM0 M) c = none) : TM0.step M (toTM0 c) = none := by
  rw [← toTM0_step, hc]
  rfl

/-! ## Inputs

Mathlib phrases computation in terms of an input list, not a configuration, so
the correspondence has to reach that far to be usable. -/

/-- The starting configuration for an input list: head on the first symbol, rest
of the input to the right, nothing to the left. -/
def ofInput (l : List Γ) : Cfg Γ Λ := ⟨default, [], l.headI, l.tail⟩

@[simp] theorem toTM0_ofInput (l : List Γ) :
    toTM0 (ofInput l : Cfg Γ Λ) = TM0.init l := by
  simp [toTM0, ofInput, TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk']

theorem step_eq_none_iff_tm0 (M : TM0.Machine Γ Λ) (c : Cfg Γ Λ) :
    step (ofTM0 M) c = none ↔ TM0.step M (toTM0 c) = none := by
  rw [← toTM0_step]
  simp

/-- **Halting agrees, on inputs.**  Mathlib's `TM0.eval` is defined on an input
list and terminates exactly when the machine here, started from that input,
reaches a configuration with no next step.  This is what carries an
undecidability theorem about `TM0.eval` over to the monoid. -/
theorem eval_dom_iff (M : TM0.Machine Γ Λ) (l : List Γ) :
    (TM0.eval M l).Dom ↔
      ∃ e, Reach (step (ofTM0 M)) (ofInput l) e ∧ step (ofTM0 M) e = none := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
    rw [TM0.eval, Part.mem_map_iff] at hb
    obtain ⟨X, hX, -⟩ := hb
    rw [StateTransition.mem_eval] at hX
    obtain ⟨hreach, hnone⟩ := hX
    rw [← toTM0_ofInput (Λ := Λ)] at hreach
    obtain ⟨e, hce, rfl⟩ := reaches_iff.mp hreach
    exact ⟨e, hce, (step_eq_none_iff_tm0 M e).mpr hnone⟩
  · rintro ⟨e, hce, hnone⟩
    have hX : toTM0 e ∈ StateTransition.eval (TM0.step M) (TM0.init l) := by
      rw [StateTransition.mem_eval]
      refine ⟨?_, (step_eq_none_iff_tm0 M e).mp hnone⟩
      rw [← toTM0_ofInput (Λ := Λ)]
      exact reaches_toTM0 hce
    rw [TM0.eval]
    exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ hX⟩

/-! ## The word problem of the presented monoid, for a Post--Turing machine -/

/-- **Word equality gives a TM0 run.**  Against a halting configuration `d`,
equality of the two words means the run from `c` arrives at `d`, hence the TM0
run from `toTM0 c` arrives at `toTM0 d`.  The rules are an explicit computable
list and the machine is Mathlib's, so this side of the correspondence is
complete. -/
theorem reaches_of_mk_eq_mk {M : TM0.Machine Γ Λ}
    {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes)
    {c d : Cfg Γ Λ} (hd : step (ofTM0 M) d = none)
    (h : StringRewriting.mk (machineSystem (ofTM0 M) states tapes) (encode c) =
      StringRewriting.mk (machineSystem (ofTM0 M) states tapes) (encode d)) :
    TM0.Reaches M (toTM0 c) (toTM0 d) :=
  reaches_toTM0 ((machineSystem_mk_eq_mk_iff_reach (ofTM0 M) hstates htapes hd).mp h)

/-- **A TM0 run gives word equality, up to the trailing-blank ambiguity.**  The
run lands on some `Cfg` with the same TM0 image as `d`, and that `Cfg` is
word-equal to `c`.  It cannot be pinned to `d` itself here, because `toTM0`
identifies tapes differing by trailing blanks; pinning it needs canonical
representatives, and no halting hypothesis is used. -/
theorem exists_mk_eq_mk_of_reaches {M : TM0.Machine Γ Λ}
    {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes)
    {c d : Cfg Γ Λ} (h : TM0.Reaches M (toTM0 c) (toTM0 d)) :
    ∃ e, toTM0 e = toTM0 d ∧
      StringRewriting.mk (machineSystem (ofTM0 M) states tapes) (encode c) =
        StringRewriting.mk (machineSystem (ofTM0 M) states tapes) (encode e) := by
  obtain ⟨e, hce, hde⟩ := reaches_iff.mp h
  exact ⟨e, hde.symm, mk_eq_mk_of_reach (presents_machineSystem _ hstates htapes) hce⟩

end PostMachine
end StringRewriting
end GroupApproximation
