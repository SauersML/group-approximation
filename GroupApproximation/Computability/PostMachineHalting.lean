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

/-! ## Completeness

A rewriting step out of a configuration word is a step of the extended machine.
The machine rules are handled by `step_complete_of_rule`; the four cleanup
shapes are done here, and each one is pinned the same way --- the state letter
of the rule has to be the state letter of the word, which fixes the state, and
the marker in the rule then fixes how much tape is left. -/

theorem hstep_complete {R : RewriteSystem (Letter Γ (HState Λ))}
    (hR : HPresents M R) (c : Cfg Γ (HState Λ)) (w : List (Letter Γ (HState Λ)))
    (hst : Step R (encode c) w) : ∃ d, hstep M c = some d ∧ w = encode d := by
  generalize hgen : encode c = z at hst
  cases hst with
  | intro u v l r hmem =>
    rcases (hR.mem_iff l r).mp hmem with hrule | hrule
    · obtain ⟨d, hd, hw⟩ := step_complete_of_rule hrule hgen
      exact ⟨d, hstep_of_step hd, hw⟩
    · obtain ⟨hu, hv⟩ := stateFree_context (c := c) hgen.symm (countP_cleanup_lhs hrule)
      rcases hrule with ⟨q, a, hM, rfl, rfl⟩ | ⟨a, x, rfl, rfl⟩ | ⟨y, a, rfl, rfl⟩ |
        ⟨a, rfl, rfl⟩
      · -- the machine has stopped: hand over to the cleanup state
        have hsplit : u ++ (Letter.state (HState.run q) :: (Letter.tape a :: v)) =
            encode c := by simpa using hgen.symm
        obtain ⟨h1, h2, h3⟩ :=
          eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
        rw [post] at h3
        obtain ⟨h4, h5⟩ := List.cons.inj h3
        have ha : a = c.head := by injection h4
        have hhalt : step (liftM M) c = none := by
          rw [step_eq_none_iff, ← h2, liftM_run, ← ha, hM]
          rfl
        refine ⟨⟨.cleanup, c.left, c.head, c.right⟩, ?_, ?_⟩
        · rw [hstep_of_halt hhalt, cleanupStep, ← h2]
        · rw [h1, h5, ha]; simp [encode, pre, post]
      · -- eat one cell on the right
        have hsplit : u ++ (Letter.state (HState.cleanup : HState Λ) ::
            (Letter.tape a :: Letter.tape x :: v)) = encode c := by simpa using hgen.symm
        obtain ⟨h1, h2, h3⟩ :=
          eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
        rw [post] at h3
        obtain ⟨h4, h5⟩ := List.cons.inj h3
        have ha : a = c.head := by injection h4
        rcases post_eq_cons h5 with ⟨_, hz, _⟩ | ⟨x', R', hcr, hz, hv'⟩
        · exact absurd hz (by simp)
        · have hx : x = x' := by injection hz
          have hhalt : step (liftM M) c = none := by
            rw [step_eq_none_iff, ← h2]; rfl
          refine ⟨⟨.cleanup, c.left, x', R'⟩, ?_, ?_⟩
          · rw [hstep_of_halt hhalt, cleanupStep, ← h2, hcr]
          · rw [h1, hv', hx]; simp [encode, pre, post]
      · -- eat one cell on the left; the marker says the right is exhausted
        have hsplit : (u ++ [Letter.tape y]) ++
            (Letter.state (HState.cleanup : HState Λ) ::
              (Letter.tape a :: Letter.endR :: v)) = encode c := by
          simpa [List.append_assoc] using hgen.symm
        obtain ⟨h1, h2, h3⟩ :=
          eq_of_stateFree_prefix (stateFree_snoc hu rfl) (stateFree_pre c)
            (hsplit.trans (encode_eq c))
        rw [post] at h3
        obtain ⟨h4, h5⟩ := List.cons.inj h3
        have ha : a = c.head := by injection h4
        rcases post_eq_cons h5 with ⟨hcr, _, hv'⟩ | ⟨_, _, _, hz, _⟩
        · rcases pre_eq_snoc h1 with ⟨_, hz', _⟩ | ⟨m, y', hu', hz', hcl⟩
          · exact absurd hz' (by simp)
          · have hy : y = y' := by injection hz'
            have hhalt : step (liftM M) c = none := by
              rw [step_eq_none_iff, ← h2]; rfl
            refine ⟨⟨.cleanup, m.reverse, y', []⟩, ?_, ?_⟩
            · rw [hstep_of_halt hhalt, cleanupStep, ← h2, hcr, hcl]
            · rw [hu', hv', hy]; simp [encode, pre, post]
        · exact absurd hz.symm (by simp)
      · -- both markers adjacent: finish
        have hsplit : (u ++ [Letter.endL]) ++
            (Letter.state (HState.cleanup : HState Λ) ::
              (Letter.tape a :: Letter.endR :: v)) = encode c := by
          simpa [List.append_assoc] using hgen.symm
        obtain ⟨h1, h2, h3⟩ :=
          eq_of_stateFree_prefix (stateFree_snoc hu rfl) (stateFree_pre c)
            (hsplit.trans (encode_eq c))
        rw [post] at h3
        obtain ⟨h4, h5⟩ := List.cons.inj h3
        have ha : a = c.head := by injection h4
        rcases post_eq_cons h5 with ⟨hcr, _, hv'⟩ | ⟨_, _, _, hz, _⟩
        · rcases pre_eq_snoc h1 with ⟨hu', _, hcl⟩ | ⟨_, _, _, hz', _⟩
          · have hhalt : step (liftM M) c = none := by
              rw [step_eq_none_iff, ← h2]; rfl
            refine ⟨doneCfg, ?_, ?_⟩
            · rw [hstep_of_halt hhalt, cleanupStep, ← h2, hcr, hcl]
            · rw [hu', hv']; simp [encode, pre, post, doneCfg]
          · exact absurd hz' (by simp)
        · exact absurd hz.symm (by simp)

/-! ## Backward closure -/

theorem hstep_closed_inv {R : RewriteSystem (Letter Γ (HState Λ))}
    (hR : HPresents M R) (c : Cfg Γ (HState Λ)) (w : List (Letter Γ (HState Λ)))
    (hst : Step R w (encode c)) : ∃ d, w = encode d := by
  generalize hgen : encode c = z at hst
  cases hst with
  | intro u v l r hmem =>
    rcases (hR.mem_iff l r).mp hmem with hrule | hrule
    · exact step_closed_inv_of_rule hrule hgen
    · obtain ⟨hu, hv⟩ := stateFree_context (c := c) hgen.symm (countP_cleanup_rhs hrule)
      rcases hrule with ⟨q, a, hM, rfl, rfl⟩ | ⟨a, x, rfl, rfl⟩ | ⟨y, a, rfl, rfl⟩ |
        ⟨a, rfl, rfl⟩
      · have hsplit : u ++ (Letter.state (HState.cleanup : HState Λ) ::
            (Letter.tape a :: v)) = encode c := by simpa using hgen.symm
        obtain ⟨h1, _, h3⟩ :=
          eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
        rw [post] at h3
        obtain ⟨_, h5⟩ := List.cons.inj h3
        exact ⟨⟨.run q, c.left, a, c.right⟩,
          by rw [h1, h5]; simp [encode, pre, post]⟩
      · have hsplit : u ++ (Letter.state (HState.cleanup : HState Λ) ::
            (Letter.tape x :: v)) = encode c := by simpa using hgen.symm
        obtain ⟨h1, _, h3⟩ :=
          eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
        rw [post] at h3
        obtain ⟨h4, h5⟩ := List.cons.inj h3
        have hx : x = c.head := by injection h4
        exact ⟨⟨.cleanup, c.left, a, x :: c.right⟩,
          by rw [h1, h5, hx]; simp [encode, pre, post]⟩
      · have hsplit : u ++ (Letter.state (HState.cleanup : HState Λ) ::
            (Letter.tape y :: Letter.endR :: v)) = encode c := by simpa using hgen.symm
        obtain ⟨h1, _, h3⟩ :=
          eq_of_stateFree_prefix hu (stateFree_pre c) (hsplit.trans (encode_eq c))
        rw [post] at h3
        obtain ⟨h4, h5⟩ := List.cons.inj h3
        have hy : y = c.head := by injection h4
        rcases post_eq_cons h5 with ⟨hcr, _, hv'⟩ | ⟨_, _, _, hz, _⟩
        · exact ⟨⟨.cleanup, c.head :: c.left, a, []⟩, by
            rw [h1, hv', hy]; simp [encode, pre, post]⟩
        · exact absurd hz.symm (by simp)
      · have hsplit : (u ++ [Letter.endL]) ++
            (Letter.state (HState.done : HState Λ) ::
              (Letter.tape default :: Letter.endR :: v)) = encode c := by
          simpa [List.append_assoc] using hgen.symm
        obtain ⟨h1, _, h3⟩ :=
          eq_of_stateFree_prefix (stateFree_snoc hu rfl) (stateFree_pre c)
            (hsplit.trans (encode_eq c))
        rw [post] at h3
        obtain ⟨_, h5⟩ := List.cons.inj h3
        rcases post_eq_cons h5 with ⟨_, _, hv'⟩ | ⟨_, _, _, hz, _⟩
        · rcases pre_eq_snoc h1 with ⟨hu', _, _⟩ | ⟨_, _, _, hz', _⟩
          · exact ⟨⟨.cleanup, [], a, []⟩, by
              rw [hu', hv']; simp [encode, pre, post]⟩
          · exact absurd hz' (by simp)
        · exact absurd hz.symm (by simp)

/-! ## The simulation, and the fixed final word -/

/-- **The extended system simulates the extended machine.**  Adding the cleanup
rules did not cost determinism on configuration words, so all four conditions
still hold. -/
def hsimulation {R : RewriteSystem (Letter Γ (HState Λ))} (hR : HPresents M R) :
    SimulationOn (Letter Γ (HState Λ)) (Cfg Γ (HState Λ)) where
  system := R
  encode := encode
  step := hstep M
  encode_injective := encode_injective
  step_sound := hstep_sound hR
  step_complete := hstep_complete hR
  step_closed_inv := hstep_closed_inv hR

/-- The final word: four letters, independent of the machine, the input, and
whatever the machine had written when it stopped. -/
def finalWord : List (Letter Γ (HState Λ)) :=
  [Letter.endL, Letter.state .done, Letter.tape default, Letter.endR]

theorem encode_doneCfg : encode (doneCfg : Cfg Γ (HState Λ)) = finalWord := by
  simp [encode, pre, post, doneCfg, finalWord]

/-- **The word problem against a fixed word is the halting problem.**  For the
extended system, `mk (encode c) = mk finalWord` says exactly that the extended
machine run from `c` reaches the final configuration --- and it gets there
precisely by stopping and then erasing.  The right-hand side no longer mentions
`c`, the tape, or the machine. -/
theorem mk_eq_finalWord_iff {R : RewriteSystem (Letter Γ (HState Λ))}
    (hR : HPresents M R) (c : Cfg Γ (HState Λ)) :
    StringRewriting.mk R (encode c) = StringRewriting.mk R finalWord ↔
      Reach (hstep M) c doneCfg := by
  rw [← encode_doneCfg]
  exact (hsimulation hR).mk_eq_mk_iff_reach_of_halts (hstep_doneCfg M)

/-! ## Reaching the final configuration is halting

What is left is to say when the extended run gets to `doneCfg`, in terms of the
original machine.  Two halves: the cleanup phase always terminates, so a machine
that stops does reach it; and a machine that never stops never leaves the
running states, so it does not. -/

/-- The original configurations, inside the extended ones. -/
def liftCfg (c : Cfg Γ Λ) : Cfg Γ (HState Λ) := ⟨.run c.q, c.left, c.head, c.right⟩

omit [Inhabited Γ] in
theorem liftCfg_injective : Function.Injective (liftCfg : Cfg Γ Λ → _) := by
  intro c d h
  cases c; cases d
  simp_all [liftCfg]

/-- The lift is a step-for-step embedding of the machine into the extended one. -/
theorem liftM_step (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    (step M c).map liftCfg = step (liftM M) (liftCfg c) := by
  unfold step liftCfg
  cases hM : M c.q c.head with
  | none => simp [hM]
  | some p =>
    obtain ⟨q', act⟩ := p
    cases act with
    | write b => simp [hM]
    | moveRight => cases c.right <;> simp [hM]
    | moveLeft => cases c.left <;> simp [hM]

theorem hstep_liftCfg_of_step {M : Machine Γ Λ} {c d : Cfg Γ Λ}
    (h : step M c = some d) : hstep M (liftCfg c) = some (liftCfg d) :=
  hstep_of_step (by rw [← liftM_step, h]; rfl)

/-- An invariant carried along a run. -/
theorem Reach.invariant {C : Type} {f : C → Option C} {P : C → Prop}
    (hP : ∀ a b, P a → f a = some b → P b) {x y : C} (h : Reach f x y) (hx : P x) :
    P y := by
  induction h with
  | refl => exact hx
  | tail _ hstep ih => exact hP _ _ ih hstep

/-! ### The cleanup phase terminates -/

/-- The three cleanup transitions, spelled out. -/
theorem hstep_cleanup_cons_right (M : Machine Γ Λ) (L : List Γ) (a x : Γ) (R : List Γ) :
    hstep M (⟨.cleanup, L, a, x :: R⟩ : Cfg Γ (HState Λ)) = some ⟨.cleanup, L, x, R⟩ := by
  rw [hstep_of_halt (by rw [step_eq_none_iff]; rfl), cleanupStep]

theorem hstep_cleanup_cons_left (M : Machine Γ Λ) (y : Γ) (L : List Γ) (a : Γ) :
    hstep M (⟨.cleanup, y :: L, a, []⟩ : Cfg Γ (HState Λ)) =
      some ⟨.cleanup, L, y, []⟩ := by
  rw [hstep_of_halt (by rw [step_eq_none_iff]; rfl), cleanupStep]

theorem hstep_cleanup_nil (M : Machine Γ Λ) (a : Γ) :
    hstep M (⟨.cleanup, [], a, []⟩ : Cfg Γ (HState Λ)) = some doneCfg := by
  rw [hstep_of_halt (by rw [step_eq_none_iff]; rfl), cleanupStep]

/-- **The cleanup phase always terminates.**  It eats the tape to the right of
the head, then the tape to its left, and each step removes a cell --- so the
induction is on the tape, and there is no appeal to a termination argument about
the machine. -/
theorem reach_doneCfg_of_cleanup (M : Machine Γ Λ) (R L : List Γ) (a : Γ) :
    Reach (hstep M) (⟨.cleanup, L, a, R⟩ : Cfg Γ (HState Λ)) doneCfg := by
  induction R generalizing L a with
  | nil =>
    induction L generalizing a with
    | nil => exact Reach.tail (Reach.refl _) (hstep_cleanup_nil M a)
    | cons y L ih => exact Reach.head (hstep_cleanup_cons_left M y L a) (ih y)
  | cons x R ih => exact Reach.head (hstep_cleanup_cons_right M L a x R) (ih L x)

/-! ### Halting one way and the other -/

theorem reach_liftCfg (M : Machine Γ Λ) {c d : Cfg Γ Λ} (h : Reach (step M) c d) :
    Reach (hstep M) (liftCfg c) (liftCfg d) := by
  induction h with
  | refl => exact Reach.refl _
  | tail _ hs ih => exact ih.tail (hstep_liftCfg_of_step hs)

theorem hstep_liftCfg_of_halt {M : Machine Γ Λ} {c : Cfg Γ Λ} (h : step M c = none) :
    hstep M (liftCfg c) = some ⟨.cleanup, c.left, c.head, c.right⟩ := by
  have hn : step (liftM M) (liftCfg c) = none := by rw [← liftM_step, h]; rfl
  rw [hstep_of_halt hn]
  simp [cleanupStep, liftCfg]

/-- A machine that stops drives the extended machine to the final
configuration: run, hand over, erase. -/
theorem reach_doneCfg_of_halts (M : Machine Γ Λ) {c e : Cfg Γ Λ}
    (hce : Reach (step M) c e) (he : step M e = none) :
    Reach (hstep M) (liftCfg c) doneCfg :=
  Reach.trans ((reach_liftCfg M hce).tail (hstep_liftCfg_of_halt he))
    (reach_doneCfg_of_cleanup M e.right e.left e.head)

/-- **A machine that never stops never gets there.**  Being the lift of a
configuration reachable from `c` is preserved by every extended step, as long as
the machine has not stopped --- and `doneCfg` is not a lift of anything, since
its state is `done` and a lift's state is `run`. -/
theorem halts_of_reach_doneCfg (M : Machine Γ Λ) {c : Cfg Γ Λ}
    (h : Reach (hstep M) (liftCfg c) doneCfg) :
    ∃ e, Reach (step M) c e ∧ step M e = none := by
  by_contra hcon
  have hcon' : ∀ e, Reach (step M) c e → step M e ≠ none := fun e he hne =>
    hcon ⟨e, he, hne⟩
  have hinv : ∀ x y : Cfg Γ (HState Λ),
      (∃ d, x = liftCfg d ∧ Reach (step M) c d) → hstep M x = some y →
      (∃ d, y = liftCfg d ∧ Reach (step M) c d) := by
    rintro x y ⟨d, rfl, hcd⟩ hxy
    obtain ⟨d', hd'⟩ := Option.ne_none_iff_exists'.mp (hcon' d hcd)
    rw [hstep_liftCfg_of_step hd'] at hxy
    exact ⟨d', (Option.some.inj hxy).symm, hcd.tail hd'⟩
  obtain ⟨d, hdone, -⟩ := Reach.invariant hinv h ⟨c, rfl, Reach.refl c⟩
  exact absurd (congrArg Cfg.q hdone) (by simp [doneCfg, liftCfg])

theorem reach_doneCfg_iff (M : Machine Γ Λ) (c : Cfg Γ Λ) :
    Reach (hstep M) (liftCfg c) doneCfg ↔
      ∃ e, Reach (step M) c e ∧ step M e = none :=
  ⟨halts_of_reach_doneCfg M, fun ⟨_, h1, h2⟩ => reach_doneCfg_of_halts M h1 h2⟩

/-- **The word problem of the presented monoid is the halting problem.**  For a
machine `M` and a starting configuration `c`, the single equation
`mk (encode (liftCfg c)) = mk finalWord` holds exactly when `M` halts from `c`.
The right-hand word is fixed --- four letters, no dependence on `M`, `c`, or the
tape --- so this is a reduction of halting to one instance of the word problem,
not a family of questions that changes with the computation. -/
theorem mk_eq_finalWord_iff_halts {R : RewriteSystem (Letter Γ (HState Λ))}
    (hR : HPresents M R) (c : Cfg Γ Λ) :
    StringRewriting.mk R (encode (liftCfg c)) =
      StringRewriting.mk R finalWord ↔
      ∃ e, Reach (step M) c e ∧ step M e = none := by
  rw [mk_eq_finalWord_iff hR]
  exact reach_doneCfg_iff M c

/-! ## The extended rule set, exhibited

As in `PostMachine`, `HPresents` says which rules a system must have without
building one.  Here it is built, as a list: the machine's rules for the lifted
machine, then the four cleanup families.  Enumerations are data, for the same
reason as before --- `Finset.toList` is noncomputable and the point of a list of
rules is that it is computable. -/

section Finite

variable (M)

/-- The rule that hands over to the cleanup state, present exactly when the
machine has no transition. -/
def haltRule (q : Λ) (a : Γ) : Option (Λ × Action Γ) →
    List (List (Letter Γ (HState Λ)) × List (Letter Γ (HState Λ)))
  | none => [([Letter.state (.run q), Letter.tape a],
              [Letter.state .cleanup, Letter.tape a])]
  | some _ => []

omit [Inhabited Γ] in
theorem mem_haltRule {q : Λ} {a : Γ} {o : Option (Λ × Action Γ)}
    {l r : List (Letter Γ (HState Λ))} :
    (l, r) ∈ haltRule q a o ↔
      (o = none ∧ l = [Letter.state (.run q), Letter.tape a] ∧
        r = [Letter.state .cleanup, Letter.tape a]) := by
  cases o <;> simp [haltRule]

/-- Every cleanup rule, as a finite list. -/
def cleanupRuleList (states : List Λ) (tapes : List Γ) :
    List (List (Letter Γ (HState Λ)) × List (Letter Γ (HState Λ))) :=
  (states.flatMap fun q => tapes.flatMap fun a => haltRule q a (M q a)) ++
  (tapes.flatMap fun a => tapes.map fun x =>
      ([Letter.state .cleanup, Letter.tape a, Letter.tape x],
       [Letter.state .cleanup, Letter.tape x])) ++
  (tapes.flatMap fun a => tapes.map fun y =>
      ([Letter.tape y, Letter.state .cleanup, Letter.tape a, Letter.endR],
       [Letter.state .cleanup, Letter.tape y, Letter.endR])) ++
  (tapes.map fun a =>
      ([Letter.endL, Letter.state .cleanup, Letter.tape a, Letter.endR],
       [Letter.endL, Letter.state .done, Letter.tape default, Letter.endR]))

/-- The extended states, enumerated from the original ones. -/
def liftStates (states : List Λ) : List (HState Λ) :=
  HState.cleanup :: HState.done :: states.map .run

omit [Inhabited Γ] in
theorem mem_liftStates {states : List Λ} (hstates : ∀ q : Λ, q ∈ states) :
    ∀ s : HState Λ, s ∈ liftStates states := by
  intro s
  cases s with
  | run q => exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map_of_mem (hstates q)))
  | cleanup => exact List.mem_cons_self
  | done => exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The full finite system: machine rules and cleanup rules. -/
def haltingSystem (states : List Λ) (tapes : List Γ) :
    RewriteSystem (Letter Γ (HState Λ)) :=
  ⟨machineRules (liftM M) (liftStates states) tapes ++ cleanupRuleList M states tapes⟩

theorem hpresents_haltingSystem {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes) :
    HPresents M (haltingSystem M states tapes) := by
  constructor
  intro l r
  have hmach := (presents_machineSystem (liftM M) (mem_liftStates hstates) htapes).mem_iff l r
  rw [haltingSystem, List.mem_append]
  rw [show (machineRules (liftM M) (liftStates states) tapes) =
      (machineSystem (liftM M) (liftStates states) tapes).rules from rfl, hmach]
  refine or_congr Iff.rfl ?_
  simp only [cleanupRuleList, List.mem_append, List.mem_flatMap, List.mem_map,
    mem_haltRule, IsCleanupRule]
  constructor
  · rintro (((⟨q, -, a, -, ho, h2, h3⟩ | ⟨a, -, x, -, h⟩) | ⟨a, -, y, -, h⟩) |
      ⟨a, -, h⟩)
    · exact Or.inl ⟨q, a, ho, h2, h3⟩
    · exact Or.inr (Or.inl ⟨a, x, congrArg Prod.fst h.symm, congrArg Prod.snd h.symm⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨y, a, congrArg Prod.fst h.symm, congrArg Prod.snd h.symm⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨a, congrArg Prod.fst h.symm, congrArg Prod.snd h.symm⟩))
  · rintro (⟨q, a, ho, rfl, rfl⟩ | ⟨a, x, rfl, rfl⟩ | ⟨y, a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨q, hstates q, a, htapes a, ho, rfl, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨a, htapes a, x, htapes x, rfl⟩))
    · exact Or.inl (Or.inr ⟨a, htapes a, y, htapes y, rfl⟩)
    · exact Or.inr ⟨a, htapes a, rfl⟩

/-- **The finite presentation whose word problem is halting.**  Everything is
explicit: the rules are a computable list built from enumerations of the state
set and the tape alphabet, the target word is four letters, and the equivalence
is with halting of the original machine. -/
theorem haltingSystem_mk_eq_finalWord_iff {states : List Λ} {tapes : List Γ}
    (hstates : ∀ q : Λ, q ∈ states) (htapes : ∀ a : Γ, a ∈ tapes) (c : Cfg Γ Λ) :
    StringRewriting.mk (haltingSystem M states tapes) (encode (liftCfg c)) =
      StringRewriting.mk (haltingSystem M states tapes) finalWord ↔
      ∃ e, Reach (step M) c e ∧ step M e = none :=
  mk_eq_finalWord_iff_halts (hpresents_haltingSystem M hstates htapes) c

end Finite

end PostMachine
end StringRewriting
end GroupApproximation
