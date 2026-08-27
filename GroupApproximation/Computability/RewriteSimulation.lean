import GroupApproximation.Computability.RewriteDeterminism

/-!
# Simulating a machine by a rewriting system

This is the piece a Post-style undecidability proof actually turns on.

A machine encoding has an easy direction and a hard one.  Easy: a machine step
is a rewriting step, so a run gives a reduction.  Hard: a *derivation* between
two configuration words is a zigzag, and it has to be shown to come from runs
of the machine.  Done concretely, for a particular machine, that argument is
long and easy to get wrong.  Done once, abstractly, it is short --- and then a
concrete encoding owes only four conditions, each a finite check against the
rule list.

Those four conditions are the fields of `Simulation`: the encoding is
injective, a machine step is a rewriting step, a rewriting step *out of a
configuration* is a machine step, and the system is deterministic.  Nothing
about tapes, states or alphabets appears.

## What is proved

`Simulation.derives_iff` is the crux: two configurations are derivable from one
another exactly when the machine can drive them to a common configuration.
`Simulation.eq_of_derives_of_halts` is the consequence a halting argument
consumes --- two *halting* configurations are derivable only if they are equal,
so distinct halts give distinct elements of the presented monoid.

The zigzag is straightened by `derives_iff_join_of_deterministic`, and the
two resulting reductions are read back as machine runs by `reach_of_reduces`.
Injectivity of the encoding then identifies the two meeting points.  That the
runs out of a single configuration are linearly ordered (`Reach.linear`) is
what makes "a common configuration" the right notion rather than an accident.
-/

namespace GroupApproximation
namespace StringRewriting

variable {α : Type*} {C : Type*}

/-! ## Runs of a partial step function -/

/-- Reachability under a partial step function: finitely many machine steps. -/
inductive Reach (step : C → Option C) : C → C → Prop where
  | refl (c : C) : Reach step c c
  | tail {c d e : C} : Reach step c d → step d = some e → Reach step c e

/-- Prepending a step.  `Reach` is built from the tail, so this needs its own
induction. -/
theorem Reach.head {step : C → Option C} {c d e : C} (h : step c = some d)
    (hde : Reach step d e) : Reach step c e := by
  induction hde with
  | refl => exact Reach.tail (Reach.refl c) h
  | tail _ hx ih => exact ih.tail hx

/-- A run is either empty or begins with a step.  `Reach` is built from the
tail, so head analysis needs its own induction. -/
theorem Reach.cases_head {step : C → Option C} {c d : C} (h : Reach step c d) :
    c = d ∨ ∃ e, step c = some e ∧ Reach step e d := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hcd hstep ih =>
    rcases ih with rfl | ⟨f, hcf, hfd⟩
    · exact Or.inr ⟨_, hstep, Reach.refl _⟩
    · exact Or.inr ⟨f, hcf, hfd.tail hstep⟩

theorem Reach.trans {step : C → Option C} {c d e : C}
    (hcd : Reach step c d) (hde : Reach step d e) : Reach step c e := by
  induction hde with
  | refl => exact hcd
  | tail _ hstep ih => exact ih.tail hstep

/-- **Runs out of a configuration are linearly ordered.**  The step function is
single-valued, so two runs from the same configuration cannot diverge; one
extends the other.  This is why "the machine drives both to a common
configuration" is the right notion. -/
theorem Reach.linear {step : C → Option C} {c d e : C}
    (hd : Reach step c d) (he : Reach step c e) :
    Reach step d e ∨ Reach step e d := by
  induction he with
  | refl => exact Or.inr hd
  | tail hce hstep ih =>
    rcases ih with h | h
    · exact Or.inl (h.tail hstep)
    · rcases Reach.cases_head h with rfl | ⟨f, hef, hfd⟩
      · exact Or.inl (Reach.tail (Reach.refl _) hstep)
      · have : f = _ := Option.some.inj (hef.symm.trans hstep)
        subst this
        exact Or.inr hfd

/-! ## Faithful encodings -/

/-- A faithful encoding of a deterministic machine as a rewriting system.

Each field is a finite check for a concrete encoding: `step_sound` and
`step_complete` are read off the rule list, `encode_injective` off the shape of
configuration words, and `deterministic` off the fact that at most one rule
matches at the unique state letter. -/
structure Simulation (α : Type*) (C : Type*) where
  /-- The rewriting system. -/
  system : RewriteSystem α
  /-- Configurations, written as words. -/
  encode : C → List α
  /-- The machine's partial step function. -/
  step : C → Option C
  /-- Distinct configurations have distinct words. -/
  encode_injective : Function.Injective encode
  /-- A machine step is a rewriting step. -/
  step_sound : ∀ c d, step c = some d → Step system (encode c) (encode d)
  /-- A rewriting step out of a configuration is a machine step. -/
  step_complete : ∀ c w, Step system (encode c) w →
    ∃ d, step c = some d ∧ w = encode d
  /-- At most one rewriting step is available anywhere. -/
  deterministic : Deterministic system

variable (S : Simulation α C)

/-- A halting configuration is a normal form: no rule applies to it. -/
theorem Simulation.normalForm_of_halts {c : C} (hc : S.step c = none) :
    NormalForm S.system (S.encode c) := by
  intro w hw
  obtain ⟨d, hd, _⟩ := S.step_complete c w hw
  rw [hc] at hd
  simp at hd

/-- **Soundness.**  A machine run gives a reduction. -/
theorem Simulation.reduces_of_reach {c d : C} (h : Reach S.step c d) :
    Reduces S.system (S.encode c) (S.encode d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (S.step_sound _ _ hstep)

/-- **Completeness.**  A reduction out of a configuration is a machine run, and
in particular never leaves the configurations. -/
theorem Simulation.reach_of_reduces {c : C} {w : List α}
    (h : Reduces S.system (S.encode c) w) :
    ∃ d, Reach S.step c d ∧ w = S.encode d := by
  induction h with
  | refl => exact ⟨c, Reach.refl c, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨d, hcd, rfl⟩ := ih
    obtain ⟨e, hde, rfl⟩ := S.step_complete d _ hstep
    exact ⟨e, hcd.tail hde, rfl⟩

/-! ## The crux -/

/-- **Derivability between configurations is meeting of machine runs.**  The
zigzag is straightened by determinism, each leg is read back as a run, and
injectivity of the encoding identifies the two meeting points. -/
theorem Simulation.derives_iff (c d : C) :
    Derives S.system (S.encode c) (S.encode d) ↔
      ∃ e, Reach S.step c e ∧ Reach S.step d e := by
  constructor
  · intro h
    obtain ⟨x, hcx, hdx⟩ :=
      (derives_iff_join_of_deterministic S.deterministic _ _).mp h
    obtain ⟨e, hce, rfl⟩ := S.reach_of_reduces hcx
    obtain ⟨e', hde', he'⟩ := S.reach_of_reduces hdx
    have hee : e' = e := S.encode_injective he'.symm
    subst hee
    exact ⟨e', hce, hde'⟩
  · rintro ⟨e, hce, hde⟩
    exact ((S.reduces_of_reach hce).derives).trans
      ((S.reduces_of_reach hde).derives).symm

/-- **Distinct halts stay distinct.**  Two halting configurations are derivable
from one another only if they are equal.  This is the statement an
undecidability argument consumes: the word problem of the presented monoid
decides which halting configuration a machine reaches. -/
theorem Simulation.eq_of_derives_of_halts {c d : C}
    (hc : S.step c = none) (hd : S.step d = none)
    (h : Derives S.system (S.encode c) (S.encode d)) : c = d := by
  obtain ⟨e, hce, hde⟩ := (S.derives_iff c d).mp h
  have hc' : c = e := by
    rcases Reach.cases_head hce with h' | ⟨f, hf, _⟩
    · exact h'
    · rw [hc] at hf
      simp at hf
  have hd' : d = e := by
    rcases Reach.cases_head hde with h' | ⟨f, hf, _⟩
    · exact h'
    · rw [hd] at hf
      simp at hf
  exact hc'.trans hd'.symm

/-- The same statement in the presented monoid, which is where the word
problem lives. -/
theorem Simulation.mk_eq_mk_iff_of_halts {c d : C}
    (hc : S.step c = none) (hd : S.step d = none) :
    StringRewriting.mk S.system (S.encode c) =
      StringRewriting.mk S.system (S.encode d) ↔ c = d := by
  constructor
  · intro h
    exact S.eq_of_derives_of_halts hc hd (StringRewriting.mk_eq_mk_iff.mp h)
  · rintro rfl
    rfl

end StringRewriting
end GroupApproximation
