import Mathlib.Data.Finite.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finite.Prod
import GroupApproximation.Computability.SemigroupWordProblemRewriting

/-!
# A deterministic Turing machine and the semi-Thue system that simulates it

This file fixes the machine model used for the Markov--Post theorem and builds
the rewriting system attached to a machine, verifying that it satisfies the
locality conditions of `SemigroupWordProblemRewriting.IsLocal`.  The simulation
theorems themselves are in `SemigroupWordProblemSimulation`; the statement of
the remaining debt is in `SemigroupWordProblem`.

## Why a bespoke machine

Mathlib's Turing machines (`Turing.TM0` and the reductions above it) carry
their tape as `Turing.ListBlank`, a quotient of lists by trailing blanks.
Encoding a quotient as a *word* forces a choice of representative and a
well-definedness argument at every step of the simulation.  The machine here
carries the tape as a pair of ordinary lists with implicit blanks off both
ends, which is the standard textbook model and makes the encoding a plain
function.  The cost of this choice is recorded honestly in the debt statement:
the universality half of Markov--Post must eventually connect this model to
Mathlib's partial recursive functions.

## The design of the rewriting system

Write `Γ` for the tape alphabet, `Λ` for the states.  A configuration
`⟨l, q, r⟩` --- left tape reversed, state, right tape starting at the scanned
cell --- is encoded as the word

```text
endL  (reverse l as tape letters)  (state q)  (scanned cell)  (rest of r)  endR
```

Every rule of the system has a left-hand side of the shape
`pre ++ control :: post` where `control` is the unique letter of weight one:

| rule | left-hand side | right-hand side |
| --- | --- | --- |
| machine step | `a, q, b, c` | see `machRhsOf` |
| eraser eats a cell | `eraseR, d` | `eraseR` |
| eraser meets the end | `eraseR, endR` | `eraseL` |
| back-eraser eats a cell | `d, eraseL` | `eraseL` |
| back-eraser meets the end | `endL, eraseL` | `done` |

Here `a` ranges over tape letters *and* `endL`, and `c` over tape letters *and*
`endR`, so a machine rule always sees a genuine letter on each side of the head
and never falls off the end: at the right end the rule inserts a fresh blank.
Because `a`, `b`, `c` are read from the word and the machine transition is a
function, the right-hand side is a *total function* of `(a, q, b, c)`, which is
exactly the `IsLocal.rhs_eq` condition.  A halting configuration converts its
state letter into the eraser, which deletes the tape and leaves the single
letter `done`.
-/

namespace GroupApproximation
namespace SemigroupWordProblem

open Relation

section Machine

variable {Γ Λ : Type}

/-- A deterministic single-tape Turing machine: a distinguished blank symbol
and a partial transition function.  `M.trans q b = some (q', b', d)` means "in
state `q` scanning `b`, write `b'`, move right if `d` and left otherwise, and
enter state `q'`"; `M.trans q b = none` means "halt". -/
structure Machine (Γ Λ : Type) where
  /-- The blank tape symbol; the tape is blank off both ends of the recorded part. -/
  blank : Γ
  /-- The transition function; `none` means the machine halts. -/
  trans : Λ → Γ → Option (Λ × Γ × Bool)

/-- A configuration: the tape to the left of the head (nearest cell first), the
state, and the tape from the scanned cell rightwards.  Cells not recorded in
either list are blank. -/
structure Cfg (Γ Λ : Type) where
  /-- The tape strictly left of the head, nearest cell first. -/
  left : List Γ
  /-- The current state. -/
  state : Λ
  /-- The tape from the scanned cell rightwards. -/
  right : List Γ

/-- The scanned symbol of a half-tape: the first recorded cell, or a blank. -/
def Machine.scan (M : Machine Γ Λ) : List Γ → Γ
  | [] => M.blank
  | b :: _ => b

/-- A half-tape with its first cell removed. -/
def tapeRest : List Γ → List Γ
  | [] => []
  | _ :: l => l

/-- The first cell of a half-tape, if it is recorded. -/
def headOpt : List Γ → Option Γ
  | [] => none
  | b :: _ => some b

/-- The machine halts at `c`: no transition applies. -/
def Machine.Halted (M : Machine Γ Λ) (c : Cfg Γ Λ) : Prop :=
  M.trans c.state (M.scan c.right) = none

/-- One step of the machine.  The two disjuncts are the right move and the left
move; on a left move the cell that was to the left of the head becomes the
scanned cell, and a blank appears when the recorded tape runs out. -/
def Machine.Step (M : Machine Γ Λ) (c c' : Cfg Γ Λ) : Prop :=
  (∃ q b, M.trans c.state (M.scan c.right) = some (q, b, true) ∧
      c' = ⟨b :: c.left, q, tapeRest c.right⟩) ∨
  (∃ q b, M.trans c.state (M.scan c.right) = some (q, b, false) ∧
      c' = ⟨tapeRest c.left, q, M.scan c.left :: b :: tapeRest c.right⟩)

/-- The machine started at `c` eventually halts. -/
def Machine.Halts (M : Machine Γ Λ) (c : Cfg Γ Λ) : Prop :=
  ∃ c', ReflTransGen M.Step c c' ∧ M.Halted c'

/-- A configuration that is not halted has a successor. -/
theorem exists_step_of_not_halted (M : Machine Γ Λ) {c : Cfg Γ Λ} (h : ¬ M.Halted c) :
    ∃ c', M.Step c c' := by
  cases htr : M.trans c.state (M.scan c.right) with
  | none => exact absurd htr h
  | some t =>
      obtain ⟨q, b, d⟩ := t
      cases d with
      | true =>
          exact ⟨⟨b :: c.left, q, tapeRest c.right⟩, Or.inl ⟨q, b, htr, rfl⟩⟩
      | false =>
          exact ⟨⟨tapeRest c.left, q, M.scan c.left :: b :: tapeRest c.right⟩,
            Or.inr ⟨q, b, htr, rfl⟩⟩

/-- No configuration reachable from a non-halting one is halted. -/
theorem not_halted_of_chain (M : Machine Γ Λ) {c c₁ : Cfg Γ Λ} (h : ¬ M.Halts c)
    (hch : ReflTransGen M.Step c c₁) : ¬ M.Halted c₁ :=
  fun hh => h ⟨c₁, hch, hh⟩

end Machine

/-! ## The alphabet -/

/-- The alphabet of the Thue system attached to a machine: tape letters, state
letters, the two end markers, the two erasers and the final letter. -/
inductive Letter (Γ Λ : Type) where
  /-- A tape symbol. -/
  | tape (b : Γ)
  /-- A state, sitting immediately left of the scanned cell. -/
  | state (q : Λ)
  /-- The left end marker. -/
  | endL
  /-- The right end marker. -/
  | endR
  /-- The eraser, travelling right. -/
  | eraseR
  /-- The eraser, travelling left. -/
  | eraseL
  /-- The final letter. -/
  | done

section Alphabet

variable {Γ Λ : Type}

/-- The weight of a letter: the control letters --- states, erasers and the
final letter --- have weight one, and every other letter weight zero.  A word
of weight one is a word with exactly one control letter, and those are the
words on which rewriting is deterministic. -/
def Letter.wt : Letter Γ Λ → ℕ
  | Letter.tape _ => 0
  | Letter.state _ => 1
  | Letter.endL => 0
  | Letter.endR => 0
  | Letter.eraseR => 1
  | Letter.eraseL => 1
  | Letter.done => 1

/-- The letter immediately left of the head: a tape letter, or the left end
marker if the recorded tape has run out. -/
def optL : Option Γ → Letter Γ Λ
  | none => Letter.endL
  | some b => Letter.tape b

/-- The letter immediately right of the scanned cell: a tape letter, or the
right end marker if the recorded tape has run out. -/
def optR : Option Γ → Letter Γ Λ
  | none => Letter.endR
  | some b => Letter.tape b

@[simp] theorem wt_optL (a : Option Γ) : Letter.wt (optL a : Letter Γ Λ) = 0 := by
  cases a <;> simp [optL, Letter.wt]

@[simp] theorem wt_optR (a : Option Γ) : Letter.wt (optR a : Letter Γ Λ) = 0 := by
  cases a <;> simp [optR, Letter.wt]

theorem optL_inj {a a' : Option Γ} (h : (optL a : Letter Γ Λ) = optL a') : a = a' := by
  cases a with
  | none =>
      cases a' with
      | none => rfl
      | some b' => simp [optL] at h
  | some b =>
      cases a' with
      | none => simp [optL] at h
      | some b' =>
          have hb : b = b' := by simpa [optL] using h
          rw [hb]

theorem optR_inj {a a' : Option Γ} (h : (optR a : Letter Γ Λ) = optR a') : a = a' := by
  cases a with
  | none =>
      cases a' with
      | none => rfl
      | some b' => simp [optR] at h
  | some b =>
      cases a' with
      | none => simp [optR] at h
      | some b' =>
          have hb : b = b' := by simpa [optR] using h
          rw [hb]

/-- A surjection onto the alphabet from a manifestly finite type. -/
def Letter.ofSum : Γ ⊕ (Λ ⊕ (Bool ⊕ (Bool ⊕ Bool))) → Letter Γ Λ
  | Sum.inl b => Letter.tape b
  | Sum.inr (Sum.inl q) => Letter.state q
  | Sum.inr (Sum.inr (Sum.inl true)) => Letter.endL
  | Sum.inr (Sum.inr (Sum.inl false)) => Letter.endR
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl true))) => Letter.eraseR
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl false))) => Letter.eraseL
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => Letter.done

theorem Letter.ofSum_surjective :
    Function.Surjective (Letter.ofSum (Γ := Γ) (Λ := Λ)) := by
  intro l
  cases l with
  | tape b => exact ⟨Sum.inl b, rfl⟩
  | state q => exact ⟨Sum.inr (Sum.inl q), rfl⟩
  | endL => exact ⟨Sum.inr (Sum.inr (Sum.inl true)), rfl⟩
  | endR => exact ⟨Sum.inr (Sum.inr (Sum.inl false)), rfl⟩
  | eraseR => exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl true))), rfl⟩
  | eraseL => exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inl false))), rfl⟩
  | done => exact ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr true))), rfl⟩

/-- **The presentation has finitely many generators**: over a finite tape
alphabet and a finite state set the letter alphabet is finite. -/
instance Letter.instFinite [Finite Γ] [Finite Λ] : Finite (Letter Γ Λ) :=
  Finite.of_surjective _ (Letter.ofSum_surjective (Γ := Γ) (Λ := Λ))

/-- Words of tape letters have weight zero. -/
@[simp] theorem weight_map_tape (u : List Γ) :
    weight Letter.wt (u.map (Letter.tape : Γ → Letter Γ Λ)) = 0 := by
  induction u with
  | nil => simp
  | cons a t ih => simp [ih, Letter.wt]

end Alphabet

/-! ## The rules -/

section Rules

variable {Γ Λ : Type}

/-- The index type of the rules: one machine rule for every left context,
state, scanned symbol and right context, and four eraser rules. -/
inductive RIdx (Γ Λ : Type) where
  /-- A machine rule, reading the letter on each side of the head. -/
  | mach (a : Option Γ) (q : Λ) (b : Γ) (c : Option Γ)
  /-- The right-travelling eraser deletes a tape cell. -/
  | eatTapeR (d : Γ)
  /-- The right-travelling eraser reaches the right end and turns around. -/
  | eatEndR
  /-- The left-travelling eraser deletes a tape cell. -/
  | eatTapeL (d : Γ)
  /-- The left-travelling eraser reaches the left end and finishes. -/
  | eatEndL

/-- A surjection onto the rule indices from a manifestly finite type. -/
def RIdx.ofSum :
    (Option Γ × Λ × Γ × Option Γ) ⊕ (Γ ⊕ (Γ ⊕ Bool)) → RIdx Γ Λ
  | Sum.inl (a, q, b, c) => RIdx.mach a q b c
  | Sum.inr (Sum.inl d) => RIdx.eatTapeR d
  | Sum.inr (Sum.inr (Sum.inl d)) => RIdx.eatTapeL d
  | Sum.inr (Sum.inr (Sum.inr true)) => RIdx.eatEndR
  | Sum.inr (Sum.inr (Sum.inr false)) => RIdx.eatEndL

theorem RIdx.ofSum_surjective :
    Function.Surjective (RIdx.ofSum (Γ := Γ) (Λ := Λ)) := by
  intro i
  cases i with
  | mach a q b c => exact ⟨Sum.inl (a, q, b, c), rfl⟩
  | eatTapeR d => exact ⟨Sum.inr (Sum.inl d), rfl⟩
  | eatEndR => exact ⟨Sum.inr (Sum.inr (Sum.inr true)), rfl⟩
  | eatTapeL d => exact ⟨Sum.inr (Sum.inr (Sum.inl d)), rfl⟩
  | eatEndL => exact ⟨Sum.inr (Sum.inr (Sum.inr false)), rfl⟩

/-- **The presentation is finite**: over a finite alphabet and a finite state
set there are finitely many rules. -/
instance RIdx.instFinite [Finite Γ] [Finite Λ] : Finite (RIdx Γ Λ) :=
  Finite.of_surjective _ (RIdx.ofSum_surjective (Γ := Γ) (Λ := Λ))

/-- The control letter of a rule. -/
def ruleSp : RIdx Γ Λ → Letter Γ Λ
  | RIdx.mach _ q _ _ => Letter.state q
  | RIdx.eatTapeR _ => Letter.eraseR
  | RIdx.eatEndR => Letter.eraseR
  | RIdx.eatTapeL _ => Letter.eraseL
  | RIdx.eatEndL => Letter.eraseL

/-- The left context of a rule. -/
def rulePre : RIdx Γ Λ → List (Letter Γ Λ)
  | RIdx.mach a _ _ _ => [optL a]
  | RIdx.eatTapeR _ => []
  | RIdx.eatEndR => []
  | RIdx.eatTapeL d => [Letter.tape d]
  | RIdx.eatEndL => [Letter.endL]

/-- The right context of a rule. -/
def rulePost : RIdx Γ Λ → List (Letter Γ Λ)
  | RIdx.mach _ _ b c => [Letter.tape b, optR c]
  | RIdx.eatTapeR d => [Letter.tape d]
  | RIdx.eatEndR => [Letter.endR]
  | RIdx.eatTapeL _ => []
  | RIdx.eatEndL => []

/-- What a right-moving head leaves to its right: the letter that was there,
or --- at the right end --- a fresh blank followed by the end marker. -/
def rightTail (blank : Γ) : Option Γ → List (Letter Γ Λ)
  | some c => [Letter.tape c]
  | none => [Letter.tape blank, Letter.endR]

/-- What a left-moving head leaves to its left: the state followed by the
letter that was there, or --- at the left end --- the end marker, the state and
a fresh blank. -/
def leftHead (blank : Γ) (q : Λ) : Option Γ → List (Letter Γ Λ)
  | some a => [Letter.state q, Letter.tape a]
  | none => [Letter.endL, Letter.state q, Letter.tape blank]

/-- The right-hand word of a machine rule, as a function of the transition
value.  On `none` (the machine halts) the state letter becomes the eraser. -/
def machRhsOf (blank : Γ) (a : Option Γ) (c : Option Γ) :
    Option (Λ × Γ × Bool) → List (Letter Γ Λ)
  | none => [optL a, Letter.eraseR, optR c]
  | some (q, b, true) => [optL a, Letter.tape b, Letter.state q] ++ rightTail blank c
  | some (q, b, false) => leftHead blank q a ++ [Letter.tape b, optR c]

/-- The right-hand word of a rule. -/
def ruleRhs (M : Machine Γ Λ) : RIdx Γ Λ → List (Letter Γ Λ)
  | RIdx.mach a q b c => machRhsOf M.blank a c (M.trans q b)
  | RIdx.eatTapeR _ => [Letter.eraseR]
  | RIdx.eatEndR => [Letter.eraseL]
  | RIdx.eatTapeL _ => [Letter.eraseL]
  | RIdx.eatEndL => [Letter.done]

@[simp] theorem weight_rightTail (blank : Γ) (c : Option Γ) :
    weight Letter.wt (rightTail blank c : List (Letter Γ Λ)) = 0 := by
  cases c <;> simp [rightTail, Letter.wt]

@[simp] theorem weight_leftHead (blank : Γ) (q : Λ) (a : Option Γ) :
    weight Letter.wt (leftHead blank q a : List (Letter Γ Λ)) = 1 := by
  cases a <;> simp [leftHead, Letter.wt]

@[simp] theorem weight_machRhsOf (blank : Γ) (a c : Option Γ)
    (t : Option (Λ × Γ × Bool)) :
    weight Letter.wt (machRhsOf blank a c t : List (Letter Γ Λ)) = 1 := by
  -- `Letter.wt` has to be unfolded for the constructor letters, but unfolding
  -- it first turns `Letter.wt (optL a)` into a raw match that `wt_optL` can no
  -- longer rewrite; casing the options lets that match reduce on its own.
  cases t with
  | none => cases a <;> cases c <;> simp [machRhsOf, Letter.wt, optL, optR]
  | some t =>
      obtain ⟨q, b, d⟩ := t
      cases d with
      | true => cases a <;> cases c <;> simp [machRhsOf, Letter.wt, optL]
      | false => cases a <;> cases c <;> simp [machRhsOf, Letter.wt, optR]

/-- **The rewriting system attached to a machine is local.**  This is the
hypothesis of every determinism and Church--Rosser statement in
`SemigroupWordProblemRewriting`. -/
theorem machine_isLocal (M : Machine Γ Λ) :
    IsLocal Letter.wt (ruleSp (Γ := Γ) (Λ := Λ)) rulePre rulePost (ruleRhs M) where
  sp_weight := by
    intro i
    cases i <;> simp [ruleSp, Letter.wt]
  pre_weight := by
    intro i
    -- Same trap as in `weight_machRhsOf`: unfolding `Letter.wt` first turns
    -- `Letter.wt (optL a)` into a raw match on `a`, which no rewrite can touch
    -- while `a` is a variable.  Casing the option lets the match reduce.
    cases i with
    | mach a q b c => cases a <;> simp [rulePre, Letter.wt, optL]
    | eatTapeR d => simp [rulePre]
    | eatEndR => simp [rulePre]
    | eatTapeL d => simp [rulePre, Letter.wt]
    | eatEndL => simp [rulePre, Letter.wt]
  post_weight := by
    intro i
    cases i with
    | mach a q b c => cases c <;> simp [rulePost, Letter.wt, optR]
    | eatTapeR d => simp [rulePost, Letter.wt]
    | eatEndR => simp [rulePost, Letter.wt]
    | eatTapeL d => simp [rulePost]
    | eatEndL => simp [rulePost]
  rhs_weight := by
    intro i
    cases i <;> simp [ruleRhs, Letter.wt]
  pre_length := by
    intro i j hsp
    cases i <;> cases j <;>
      first
        | rfl
        | exact absurd hsp (by simp [ruleSp])
  post_length := by
    intro i j hsp
    cases i <;> cases j <;>
      first
        | rfl
        | exact absurd hsp (by simp [ruleSp])
  rhs_eq := by
    intro i j hpre hsp hpost
    cases i with
    | mach a q b c =>
        cases j with
        | mach a' q' b' c' =>
            have hpre' : ([optL a] : List (Letter Γ Λ)) = [optL a'] := hpre
            have hsp' : (Letter.state q : Letter Γ Λ) = Letter.state q' := hsp
            have hpost' : ([Letter.tape b, optR c] : List (Letter Γ Λ))
                = [Letter.tape b', optR c'] := hpost
            have ha : a = a' := optL_inj (List.cons.inj hpre').1
            have hq : q = q' := Letter.state.inj hsp'
            have hb : b = b' := Letter.tape.inj (List.cons.inj hpost').1
            have hc : c = c' :=
              optR_inj (List.cons.inj (List.cons.inj hpost').2).1
            rw [ha, hq, hb, hc]
        | eatTapeR d =>
            have h : (Letter.state q : Letter Γ Λ) = Letter.eraseR := hsp
            simp at h
        | eatEndR =>
            have h : (Letter.state q : Letter Γ Λ) = Letter.eraseR := hsp
            simp at h
        | eatTapeL d =>
            have h : (Letter.state q : Letter Γ Λ) = Letter.eraseL := hsp
            simp at h
        | eatEndL =>
            have h : (Letter.state q : Letter Γ Λ) = Letter.eraseL := hsp
            simp at h
    | eatTapeR d =>
        cases j with
        | mach a' q' b' c' =>
            have h : (Letter.eraseR : Letter Γ Λ) = Letter.state q' := hsp
            simp at h
        | eatTapeR d' => rfl
        | eatEndR =>
            have h : ([Letter.tape d] : List (Letter Γ Λ)) = [Letter.endR] := hpost
            simp at h
        | eatTapeL d' =>
            have h : (Letter.eraseR : Letter Γ Λ) = Letter.eraseL := hsp
            simp at h
        | eatEndL =>
            have h : (Letter.eraseR : Letter Γ Λ) = Letter.eraseL := hsp
            simp at h
    | eatEndR =>
        cases j with
        | mach a' q' b' c' =>
            have h : (Letter.eraseR : Letter Γ Λ) = Letter.state q' := hsp
            simp at h
        | eatTapeR d' =>
            have h : ([Letter.endR] : List (Letter Γ Λ)) = [Letter.tape d'] := hpost
            simp at h
        | eatEndR => rfl
        | eatTapeL d' =>
            have h : (Letter.eraseR : Letter Γ Λ) = Letter.eraseL := hsp
            simp at h
        | eatEndL =>
            have h : (Letter.eraseR : Letter Γ Λ) = Letter.eraseL := hsp
            simp at h
    | eatTapeL d =>
        cases j with
        | mach a' q' b' c' =>
            have h : (Letter.eraseL : Letter Γ Λ) = Letter.state q' := hsp
            simp at h
        | eatTapeR d' =>
            have h : (Letter.eraseL : Letter Γ Λ) = Letter.eraseR := hsp
            simp at h
        | eatEndR =>
            have h : (Letter.eraseL : Letter Γ Λ) = Letter.eraseR := hsp
            simp at h
        | eatTapeL d' => rfl
        | eatEndL =>
            have h : ([Letter.tape d] : List (Letter Γ Λ)) = [Letter.endL] := hpre
            simp at h
    | eatEndL =>
        cases j with
        | mach a' q' b' c' =>
            have h : (Letter.eraseL : Letter Γ Λ) = Letter.state q' := hsp
            simp at h
        | eatTapeR d' =>
            have h : (Letter.eraseL : Letter Γ Λ) = Letter.eraseR := hsp
            simp at h
        | eatEndR =>
            have h : (Letter.eraseL : Letter Γ Λ) = Letter.eraseR := hsp
            simp at h
        | eatTapeL d' =>
            have h : ([Letter.endL] : List (Letter Γ Λ)) = [Letter.tape d'] := hpre
            simp at h
        | eatEndL => rfl

/-- Every left-hand word has at least two letters; in particular the one-letter
word `done` is a normal form. -/
theorem two_le_length_lhsWord (i : RIdx Γ Λ) :
    2 ≤ (lhsWord ruleSp rulePre rulePost i).length := by
  cases i <;> simp [lhsWord, rulePre, rulePost]

/-- `done` admits no rewrite. -/
theorem done_normalForm (M : Machine Γ Λ) :
    ∀ z, ¬ Step ruleSp rulePre rulePost (ruleRhs M) [Letter.done] z := by
  rintro z ⟨i, x, y, hx, -⟩
  have hlen := congrArg List.length hx
  have h2 := two_le_length_lhsWord (Γ := Γ) (Λ := Λ) i
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

end Rules

end SemigroupWordProblem
end GroupApproximation
