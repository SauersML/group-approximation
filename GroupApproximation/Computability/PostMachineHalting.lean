import GroupApproximation.Computability.PostMachine

/-!
# Collapsing every halt to one word

`Computability.PostMachine` makes the word problem of the presented monoid the
machine's *reachability* problem: `mk (encode c) = mk (encode d)` exactly when
the run from `c` arrives at the halting configuration `d`.  That is not yet the
halting problem, because `d` still names a whole tape.  A universal machine
halts with whatever it computed written on the tape, so "reaches *this* halt" is
not "halts".

The classical repair is to erase.  After the machine stops, a cleanup phase eats
the tape one cell at a time and ends in a single configuration that does not
depend on where the machine stopped.  Then "halts" and "reaches the one final
configuration" are the same statement, and the word problem asks it against a
*fixed* word.

## Why the erasing is not a machine step

A `Cfg` step writes and moves; it cannot delete a cell, and the machine cannot
even tell where the written tape ends, since a blank in the middle of the tape
looks like a blank past the end.  The rewriting system can tell: it sees the end
markers.  So the cleanup lives in the *rules*, not in the transition function ---
which is exactly why Post's construction is a statement about rewriting systems
rather than about machines.

## Keeping the framework

Extra rules would ordinarily break `SimulationOn`, whose `step_complete` says a
rewriting step out of a configuration is a *machine* step.  Two choices keep it
intact.

First, the cleanup states are folded into the state type (`HState`), so cleanup
configurations are ordinary `Cfg`s and the encoding is unchanged --- no second
word shape, and every letter-level lemma of `PostMachine` applies verbatim.

Second, the erasing rules are written so that at most one applies to any
configuration word: eating on the right requires a tape letter after the head,
eating on the left requires the *right* marker immediately after the head, and
finishing requires both markers adjacent.  The extended system is therefore
still deterministic on configuration words, so it is a `SimulationOn` for the
extended step function, and `mk_eq_mk_iff_reach_of_halts` applies to it with the
final configuration --- whose word is `endL, done, blank, endR`, independent of
the machine and of the input.
-/

namespace GroupApproximation
namespace StringRewriting
namespace PostMachine

variable {Γ Λ : Type}

/-- The state type of the extended machine: the original states, a cleanup
state, and the single final state. -/
inductive HState (Λ : Type) where
  | run : Λ → HState Λ
  | cleanup : HState Λ
  | done : HState Λ
  deriving DecidableEq

/-- The original machine, on the extended state type.  The two new states have
no transitions: what they do is done by rules, not by the machine. -/
def liftM (M : Machine Γ Λ) : Machine Γ (HState Λ)
  | .run q, a => (M q a).map fun p => (HState.run p.1, p.2)
  | .cleanup, _ => none
  | .done, _ => none

@[simp] theorem liftM_run (M : Machine Γ Λ) (q : Λ) (a : Γ) :
    liftM M (.run q) a = (M q a).map (fun p => (HState.run p.1, p.2)) := rfl

@[simp] theorem liftM_cleanup (M : Machine Γ Λ) (a : Γ) :
    liftM M .cleanup a = none := rfl

@[simp] theorem liftM_done (M : Machine Γ Λ) (a : Γ) :
    liftM M .done a = none := rfl

variable [Inhabited Γ]

/-- The final configuration: the one every halting run ends at. -/
def doneCfg : Cfg Γ (HState Λ) := ⟨.done, [], default, []⟩

/-- What the cleanup phase does.  Eat the tape to the right of the head, then
the tape to its left, then finish.  On a running state this only fires when the
machine has stopped, which is where `hstep` puts it. -/
def cleanupStep : Cfg Γ (HState Λ) → Option (Cfg Γ (HState Λ)) := fun c =>
  match c.q with
  | .run _ => some ⟨.cleanup, c.left, c.head, c.right⟩
  | .cleanup =>
      match c.right with
      | x :: R => some ⟨.cleanup, c.left, x, R⟩
      | [] =>
          match c.left with
          | y :: L => some ⟨.cleanup, L, y, []⟩
          | [] => some doneCfg
  | .done => none

/-- The extended step function: the machine while it runs, the cleanup after it
stops. -/
def hstep (M : Machine Γ Λ) : Cfg Γ (HState Λ) → Option (Cfg Γ (HState Λ)) :=
  fun c =>
    match step (liftM M) c with
    | some d => some d
    | none => cleanupStep c

theorem hstep_of_step {M : Machine Γ Λ} {c d : Cfg Γ (HState Λ)}
    (h : step (liftM M) c = some d) : hstep M c = some d := by
  unfold hstep; rw [h]

theorem hstep_of_halt {M : Machine Γ Λ} {c : Cfg Γ (HState Λ)}
    (h : step (liftM M) c = none) : hstep M c = cleanupStep c := by
  unfold hstep; rw [h]

/-- The final configuration is final. -/
@[simp] theorem hstep_doneCfg (M : Machine Γ Λ) :
    hstep M (doneCfg : Cfg Γ (HState Λ)) = none := by
  unfold hstep step cleanupStep doneCfg
  simp

/-! ## The cleanup rules -/

variable (M : Machine Γ Λ)

/-- The four rules the machine does not provide: hand over to the cleanup state
when the machine stops, eat one cell on the right, eat one cell on the left, and
finish.  Each carries exactly one state letter on each side, and at most one
applies to any configuration word --- the right-hand marker in the third and
fourth shapes is what makes them exclusive. -/
def IsCleanupRule (l r : List (Letter Γ (HState Λ))) : Prop :=
  (∃ q a, M q a = none ∧
      l = [Letter.state (.run q), Letter.tape a] ∧
      r = [Letter.state .cleanup, Letter.tape a]) ∨
  (∃ a x,
      l = [Letter.state .cleanup, Letter.tape a, Letter.tape x] ∧
      r = [Letter.state .cleanup, Letter.tape x]) ∨
  (∃ y a,
      l = [Letter.tape y, Letter.state .cleanup, Letter.tape a, Letter.endR] ∧
      r = [Letter.state .cleanup, Letter.tape y, Letter.endR]) ∨
  (∃ a,
      l = [Letter.endL, Letter.state .cleanup, Letter.tape a, Letter.endR] ∧
      r = [Letter.endL, Letter.state .done, Letter.tape default, Letter.endR])

/-- A system presenting the machine's rules together with the cleanup rules. -/
structure HPresents (R : RewriteSystem (Letter Γ (HState Λ))) : Prop where
  mem_iff : ∀ l r, (l, r) ∈ R.rules ↔
    (IsMachineRule (liftM M) l r ∨ IsCleanupRule M l r)

variable {M}

theorem countP_cleanup_lhs {l r : List (Letter Γ (HState Λ))}
    (h : IsCleanupRule M l r) : l.countP isState = 1 := by
  rcases h with ⟨q, a, _, rfl, _⟩ | ⟨a, x, rfl, _⟩ | ⟨y, a, rfl, _⟩ |
    ⟨a, rfl, _⟩ <;> simp

theorem countP_cleanup_rhs {l r : List (Letter Γ (HState Λ))}
    (h : IsCleanupRule M l r) : r.countP isState = 1 := by
  rcases h with ⟨q, a, _, _, rfl⟩ | ⟨a, x, _, rfl⟩ | ⟨y, a, _, rfl⟩ |
    ⟨a, _, rfl⟩ <;> simp

/-! ## Soundness -/

theorem hstep_sound {R : RewriteSystem (Letter Γ (HState Λ))} (hR : HPresents M R)
    (c d : Cfg Γ (HState Λ)) (h : hstep M c = some d) :
    Step R (encode c) (encode d) := by
  have hsub : ∀ l r, IsMachineRule (liftM M) l r → (l, r) ∈ R.rules :=
    fun l r hlr => (hR.mem_iff l r).mpr (Or.inl hlr)
  cases hm : step (liftM M) c with
  | some e =>
    rw [hstep_of_step hm] at h
    rw [← Option.some.inj h]
    exact step_sound_of_subset hsub c e hm
  | none =>
    rw [hstep_of_halt hm, cleanupStep] at h
    -- the cleanup rules, one configuration shape at a time
    match hq : c.q with
    | .run q =>
      rw [hq] at h
      have hd : d = ⟨.cleanup, c.left, c.head, c.right⟩ := (Option.some.inj h).symm
      have hM : M q c.head = none := by
        have hlift := (step_eq_none_iff c).mp hm
        rw [hq, liftM_run] at hlift
        simpa using hlift
      have hmem := (hR.mem_iff _ _).mpr
        (Or.inr (Or.inl ⟨q, c.head, hM, rfl, rfl⟩))
      have h1 : encode c =
          pre c ++ [Letter.state (HState.run q), Letter.tape c.head] ++
            (c.right.map Letter.tape ++ [Letter.endR]) := by
        rw [← hq]; simp [encode, post, List.append_assoc]
      have h2 : encode d =
          pre c ++ [Letter.state (HState.cleanup : HState Λ), Letter.tape c.head] ++
            (c.right.map Letter.tape ++ [Letter.endR]) := by
        rw [hd]; simp [encode, pre, post]
      rw [h1, h2]
      exact Step.intro _ _ _ _ hmem
    | .cleanup =>
      rw [hq] at h
      match hr : c.right with
      | x :: R =>
        rw [hr] at h
        have hd : d = ⟨.cleanup, c.left, x, R⟩ := (Option.some.inj h).symm
        have hmem := (hR.mem_iff _ _).mpr (Or.inr (Or.inr (Or.inl ⟨c.head, x, rfl, rfl⟩)))
        have h1 : encode c =
            pre c ++ [Letter.state (HState.cleanup : HState Λ), Letter.tape c.head,
              Letter.tape x] ++ (R.map Letter.tape ++ [Letter.endR]) := by
          rw [← hq]; simp [encode, post, hr, List.append_assoc]
        have h2 : encode d =
            pre c ++ [Letter.state (HState.cleanup : HState Λ), Letter.tape x] ++
              (R.map Letter.tape ++ [Letter.endR]) := by
          rw [hd]; simp [encode, pre, post]
        rw [h1, h2]
        exact Step.intro _ _ _ _ hmem
      | [] =>
        rw [hr] at h
        match hl : c.left with
        | y :: L =>
          rw [hl] at h
          have hd : d = ⟨.cleanup, L, y, []⟩ := (Option.some.inj h).symm
          have hmem := (hR.mem_iff _ _).mpr
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨y, c.head, rfl, rfl⟩))))
          have h1 : encode c =
              (Letter.endL :: L.reverse.map Letter.tape) ++
                [Letter.tape y, Letter.state (HState.cleanup : HState Λ),
                  Letter.tape c.head, Letter.endR] ++ [] := by
            rw [← hq]; simp [encode, pre, post, hl, hr]
          have h2 : encode d =
              (Letter.endL :: L.reverse.map Letter.tape) ++
                [Letter.state (HState.cleanup : HState Λ), Letter.tape y,
                  Letter.endR] ++ [] := by
            rw [hd]; simp [encode, pre, post]
          rw [h1, h2]
          exact Step.intro _ _ _ _ hmem
        | [] =>
          rw [hl] at h
          have hd : d = (doneCfg : Cfg Γ (HState Λ)) := (Option.some.inj h).symm
          have hmem := (hR.mem_iff _ _).mpr
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨c.head, rfl, rfl⟩))))
          have h1 : encode c =
              [] ++ [Letter.endL, Letter.state (HState.cleanup : HState Λ),
                Letter.tape c.head, Letter.endR] ++ [] := by
            rw [← hq]; simp [encode, pre, post, hl, hr]
          have h2 : encode d =
              [] ++ [Letter.endL, Letter.state (HState.done : HState Λ),
                Letter.tape default, Letter.endR] ++ [] := by
            rw [hd]; simp [encode, pre, post, doneCfg]
          rw [h1, h2]
          exact Step.intro _ _ _ _ hmem
    | .done =>
      rw [hq] at h
      exact absurd h (by simp)

end PostMachine
end StringRewriting
end GroupApproximation
