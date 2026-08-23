import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-!
# Finite deterministic automata for word certificates

This module is a small, group-independent foundation for replaying finite
normal-form certificates.  A `WordDFA` has a finite state type, a deterministic
transition for every letter, and a Boolean accepting predicate.  The finite
predicate `AcceptingCycleChecks` records three literal words:

* a prefix reaching a state;
* a nonempty loop returning to that state;
* a suffix reaching an accepting state.

All equalities in that predicate are decidable when the alphabet has decidable
equality.  The pumping theorem below proves directly that a checked productive
cycle supplies accepted words of arbitrarily large length.  It deliberately
makes no claim about groups, normal-form uniqueness, hyperbolicity, or torsion;
those require additional certificates.
-/

namespace GroupApproximation
namespace FiniteWordAutomaton

universe u v

/-- A deterministic word automaton with a finite state space.  Acceptance is
Boolean so a concrete transition table can be checked by kernel evaluation. -/
structure WordDFA (Alphabet : Type u) (State : Type v)
    [Fintype State] where
  start : State
  step : State → Alphabet → State
  accepting : State → Bool

variable {Alphabet : Type u} {State : Type v} [Fintype State]

namespace WordDFA

/-- Run an automaton from an arbitrary state. -/
def run (M : WordDFA Alphabet State) : State → List Alphabet → State
  | q, [] => q
  | q, a :: w => run M (M.step q a) w

@[simp] theorem run_nil (M : WordDFA Alphabet State) (q : State) :
    M.run q [] = q := rfl

@[simp] theorem run_cons (M : WordDFA Alphabet State) (q : State)
    (a : Alphabet) (w : List Alphabet) :
    M.run q (a :: w) = M.run (M.step q a) w := rfl

/-- Running a concatenation is running its two factors successively. -/
theorem run_append (M : WordDFA Alphabet State) (q : State)
    (u v : List Alphabet) :
    M.run q (u ++ v) = M.run (M.run q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons a u ih =>
      simp only [List.cons_append, run_cons]
      exact ih (M.step q a)

/-- The language accepted from the distinguished initial state. -/
def Accepts (M : WordDFA Alphabet State) (w : List Alphabet) : Prop :=
  M.accepting (M.run M.start w) = true

instance (M : WordDFA Alphabet State) (w : List Alphabet) :
    Decidable (M.Accepts w) := by
  unfold Accepts
  infer_instance

end WordDFA

/-- Repeat a literal word `n` times.  This recursive version keeps the pumping
proof independent of monoid-power simplification. -/
def repeatWord (cycleWord : List Alphabet) : ℕ → List Alphabet
  | 0 => []
  | n + 1 => cycleWord ++ repeatWord cycleWord n

@[simp] theorem repeatWord_zero (cycleWord : List Alphabet) :
    repeatWord cycleWord 0 = [] := rfl

@[simp] theorem repeatWord_succ (cycleWord : List Alphabet) (n : ℕ) :
    repeatWord cycleWord (n + 1) =
      cycleWord ++ repeatWord cycleWord n := rfl

@[simp] theorem length_repeatWord (cycleWord : List Alphabet) (n : ℕ) :
    (repeatWord cycleWord n).length = n * cycleWord.length := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [repeatWord_succ, List.length_append, ih]
      simp [Nat.succ_mul, Nat.add_comm]

/-- Literal finite data for a productive accepting cycle. -/
structure PumpingData (Alphabet : Type u) where
  prefixWord : List Alphabet
  cycleWord : List Alphabet
  suffixWord : List Alphabet

/-- The finite checks on `PumpingData`.  The loop is based at the state reached
by the prefix, and the suffix from that state is accepting. -/
def AcceptingCycleChecks (M : WordDFA Alphabet State)
    (C : PumpingData Alphabet) : Prop :=
  C.cycleWord ≠ [] ∧
    M.run (M.run M.start C.prefixWord) C.cycleWord =
      M.run M.start C.prefixWord ∧
    M.accepting
      (M.run (M.run M.start C.prefixWord) C.suffixWord) = true

instance [DecidableEq Alphabet] [DecidableEq State]
    (M : WordDFA Alphabet State) (C : PumpingData Alphabet) :
    Decidable (AcceptingCycleChecks M C) := by
  unfold AcceptingCycleChecks
  infer_instance

/-- The word obtained by traversing the certified loop `n` times. -/
def pumpedWord (C : PumpingData Alphabet) (n : ℕ) : List Alphabet :=
  C.prefixWord ++ repeatWord C.cycleWord n ++ C.suffixWord

@[simp] theorem length_pumpedWord (C : PumpingData Alphabet) (n : ℕ) :
    (pumpedWord C n).length =
      C.prefixWord.length + n * C.cycleWord.length + C.suffixWord.length := by
  simp [pumpedWord, List.length_append, Nat.add_assoc]

/-- A loop returning to `q` can be traversed any number of times. -/
theorem run_repeatWord_of_run_eq (M : WordDFA Alphabet State) (q : State)
    (cycleWord : List Alphabet) (hcycle : M.run q cycleWord = q) (n : ℕ) :
    M.run q (repeatWord cycleWord n) = q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repeatWord_succ, M.run_append, hcycle]
      exact ih

/-- Every word obtained by pumping a checked productive cycle is accepted. -/
theorem accepts_pumpedWord (M : WordDFA Alphabet State)
    (C : PumpingData Alphabet) (hC : AcceptingCycleChecks M C) (n : ℕ) :
    M.Accepts (pumpedWord C n) := by
  rcases hC with ⟨-, hcycle, haccept⟩
  unfold WordDFA.Accepts pumpedWord
  rw [M.run_append, M.run_append,
    run_repeatWord_of_run_eq M (M.run M.start C.prefixWord)
      C.cycleWord hcycle n]
  exact haccept

/-- **Accepting-cycle infinitude certificate, quantitative form.**  A checked
reachable productive cycle gives accepted words of arbitrarily large length.
This is the exact conclusion needed before a separate uniqueness certificate
can turn accepted normal forms into infinitely many represented elements. -/
theorem exists_accepted_word_of_length_ge (M : WordDFA Alphabet State)
    (C : PumpingData Alphabet) (hC : AcceptingCycleChecks M C) (L : ℕ) :
    ∃ w : List Alphabet, M.Accepts w ∧ L ≤ w.length := by
  refine ⟨pumpedWord C L, accepts_pumpedWord M C hC L, ?_⟩
  have hcycleLengthNe : C.cycleWord.length ≠ 0 := by
    simpa using hC.1
  have hcyclePos : 0 < C.cycleWord.length :=
    Nat.pos_of_ne_zero hcycleLengthNe
  rw [length_pumpedWord]
  have hmul : L ≤ L * C.cycleWord.length := by
    exact Nat.le_mul_of_pos_right L hcyclePos
  omega

end FiniteWordAutomaton
end GroupApproximation
