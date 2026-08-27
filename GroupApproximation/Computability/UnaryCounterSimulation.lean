import GroupApproximation.Computability.RewriteSimulation

/-!
# A worked instance of the simulation interface

`Computability.RewriteSimulation` reduced a machine encoding to four
conditions.  An abstract interface nobody has instantiated is a liability
rather than an asset: the conditions might be unsatisfiable, or satisfiable
only after reformulating them.  This file discharges all four for a concrete
machine, so the interface is known to be usable and there is a template to
copy when the real encoding is written.

The machine is the smallest one with a genuine step function: a unary counter
that decrements and halts at zero.  Its alphabet is `Unit`, which makes the
system deterministic *globally* rather than only on configuration words ---
over a one-letter alphabet every word is a power of the letter, so removing a
letter anywhere gives the same result.  That is what lets `deterministic` be
discharged outright, and it is the property a real encoding has to arrange by
other means (one state letter per configuration word).

The presented monoid here is trivial, which is expected: the point of the file
is that `step_complete` and `deterministic` are *real* proofs about arbitrary
rewriting steps, not that the resulting monoid is interesting.
-/

namespace GroupApproximation
namespace StringRewriting
namespace UnaryCounter

/-- Every list over `Unit` is a power of the unique letter.  This is what makes
the one-letter alphabet deterministic. -/
theorem eq_replicate (l : List Unit) : l = List.replicate l.length () := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases a
    rw [List.length_cons, List.replicate_succ]
    exact congrArg (fun s => () :: s) ih

/-- Lists over `Unit` of equal length are equal. -/
theorem eq_of_length_eq {l m : List Unit} (h : l.length = m.length) : l = m := by
  rw [eq_replicate l, eq_replicate m, h]

/-- The counter system: one rule, deleting the unique letter. -/
def system : RewriteSystem Unit := ⟨[([()], [])]⟩

theorem mem_rules_iff {p : List Unit × List Unit} :
    p ∈ system.rules ↔ p = ([()], []) := by
  simp [system]

/-- Configurations are natural numbers, written in unary. -/
def encode (n : ℕ) : List Unit := List.replicate n ()

theorem encode_injective : Function.Injective encode := by
  intro m n h
  have := congrArg List.length h
  simpa [encode] using this

/-- The counter decrements, and halts at zero. -/
def step : ℕ → Option ℕ
  | 0 => none
  | n + 1 => some n

/-! ## The four conditions -/

theorem step_sound (c d : ℕ) (h : step c = some d) :
    Step system (encode c) (encode d) := by
  cases c with
  | zero => exact absurd h (by simp [step])
  | succ n =>
    have hd : d = n := by simpa [step] using h.symm
    rw [hd]
    have hsplit : encode (n + 1) = [] ++ [()] ++ encode n := by
      simp [encode, List.replicate_succ]
    have hres : encode n = [] ++ [] ++ encode n := by simp
    rw [hsplit, hres]
    exact Step.intro [] (encode n) [()] [] (by simp [system])

/-- A rewriting step deletes exactly one letter, so it lands on the predecessor
configuration.  This is the condition that does real work: it quantifies over
*every* way a rule can match. -/
theorem step_complete (c : ℕ) (w : List Unit) (h : Step system (encode c) w) :
    ∃ d, step c = some d ∧ w = encode d := by
  generalize hx : encode c = x at h
  cases h with
  | intro u v l r hr =>
    rw [mem_rules_iff] at hr
    have hl : l = [()] := congrArg Prod.fst hr
    have hrr : r = [] := congrArg Prod.snd hr
    subst hl
    subst hrr
    have hlen : c = u.length + (v.length + 1) := by
      have hc := congrArg List.length hx
      simpa [encode] using hc
    refine ⟨u.length + v.length, ?_, ?_⟩
    · have hcpos : c = (u.length + v.length) + 1 := by omega
      rw [hcpos]
      rfl
    · have hl2 : (u ++ [] ++ v).length = u.length + v.length := by simp
      rw [eq_replicate (u ++ [] ++ v), hl2]
      rfl

/-- Determinism: over a one-letter alphabet the result of deleting a letter
does not depend on which letter was deleted. -/
theorem deterministic : Deterministic system := by
  intro a b c hb hc
  have hlb : b.length + 1 = a.length := by
    cases hb with
    | intro u v l r hr =>
      rw [mem_rules_iff] at hr
      have hl : l = [()] := congrArg Prod.fst hr
      have hrr : r = [] := congrArg Prod.snd hr
      subst hl; subst hrr
      simp only [List.length_append, List.length_nil, List.length_cons]
      omega
  have hlc : c.length + 1 = a.length := by
    cases hc with
    | intro u v l r hr =>
      rw [mem_rules_iff] at hr
      have hl : l = [()] := congrArg Prod.fst hr
      have hrr : r = [] := congrArg Prod.snd hr
      subst hl; subst hrr
      simp only [List.length_append, List.length_nil, List.length_cons]
      omega
  exact eq_of_length_eq (by omega)

/-- **The interface is inhabited.**  All four conditions hold for a concrete
machine, so a real encoding has a template to follow and the conditions are
known to be satisfiable. -/
def simulation : Simulation Unit ℕ where
  system := system
  encode := encode
  step := step
  encode_injective := encode_injective
  step_sound := step_sound
  step_complete := step_complete
  deterministic := deterministic

/-- The abstract theorems specialize: the counter reaches a common
configuration from any two derivably-equal ones. -/
theorem derives_iff (c d : ℕ) :
    Derives system (encode c) (encode d) ↔
      ∃ e, Reach step c e ∧ Reach step d e :=
  simulation.derives_iff c d

/-- Zero is the only halting configuration, so the separation statement is
sharp here: distinct halts would be distinct, and there is exactly one. -/
theorem step_eq_none_iff (c : ℕ) : step c = none ↔ c = 0 := by
  cases c with
  | zero => simp [step]
  | succ n => simp [step]

end UnaryCounter
end StringRewriting
end GroupApproximation
