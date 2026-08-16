import GroupApproximation.Computability.RewriteConfluence

/-!
# Deterministic systems are confluent

`Computability.RewriteConfluence` showed that confluence straightens a
derivation.  This file supplies confluence in the case a machine encoding
actually produces.

A rewriting system encoding a *deterministic* machine has the property that at
most one rule applies to a configuration word, at one position: the rules are
written so that each consumes the unique state letter, and the machine's
transition function is single-valued.  Such a system is deterministic as a
rewriting system, and determinism gives confluence outright --- no critical
pair analysis, no Newman's lemma, no termination hypothesis.

The proof is an induction from the head of the first reduction.  At each step
either the second reduction has already stopped, in which case the first
reduction is itself the join, or both take a step, and determinism forces those
steps to agree so the induction hypothesis applies.  Nothing else is used.

Combined with `derives_iff_join`, this yields
`eq_of_derives_of_normalForm_of_deterministic`: in a deterministic system two
distinct normal forms are never derivable.  That is the statement a halting
argument consumes --- a machine that halts in a distinguished configuration
gives a normal form, and a machine that halts differently gives a different
one, so the two are not equal in the presented monoid.
-/

namespace GroupApproximation
namespace StringRewriting

variable {α : Type*}

/-- A system is deterministic when at most one rewriting step is available
from any word. -/
def Deterministic (R : RewriteSystem α) : Prop :=
  ∀ a b c, Step R a b → Step R a c → b = c

/-- **Determinism gives confluence.**  No critical pairs and no termination
hypothesis are needed: if there is only ever one step to take, two reductions
out of a word are prefixes of one another. -/
theorem confluent_of_deterministic {R : RewriteSystem α}
    (hdet : Deterministic R) : Confluent R := by
  intro a b c hab hac
  revert c
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro c hac
    exact ⟨c, hac, Relation.ReflTransGen.refl⟩
  | head hstep htail ih =>
    intro c hac
    rcases Relation.ReflTransGen.cases_head hac with heq | ⟨a'', hstep', hrest⟩
    · subst heq
      exact ⟨_, Relation.ReflTransGen.refl, Relation.ReflTransGen.head hstep htail⟩
    · have hEq := hdet _ _ _ hstep hstep'
      subst hEq
      exact ih c hrest

/-- In a deterministic system, two distinct normal forms are never derivable
from one another.  This is the form a halting argument consumes. -/
theorem eq_of_derives_of_normalForm_of_deterministic {R : RewriteSystem α}
    (hdet : Deterministic R) {a b : List α}
    (ha : NormalForm R a) (hb : NormalForm R b) (h : Derives R a b) : a = b :=
  eq_of_derives_of_normalForm (confluent_of_deterministic hdet) ha hb h

/-- The same statement in the presented monoid. -/
theorem mk_ne_mk_of_normalForm_of_deterministic {R : RewriteSystem α}
    (hdet : Deterministic R) {a b : List α}
    (ha : NormalForm R a) (hb : NormalForm R b) (hab : a ≠ b) :
    mk R a ≠ mk R b :=
  mk_ne_mk_of_normalForm (confluent_of_deterministic hdet) ha hb hab

/-- **Derivability in a deterministic system is a join of directed
reductions.**  Stated separately because this is the form in which a
simulation uses it: a derivation between two configuration words is replaced
by two runs of the machine meeting at a common configuration. -/
theorem derives_iff_join_of_deterministic {R : RewriteSystem α}
    (hdet : Deterministic R) (a b : List α) :
    Derives R a b ↔ ∃ c, Reduces R a c ∧ Reduces R b c :=
  derives_iff_join (confluent_of_deterministic hdet) a b

/-- The empty system is deterministic, since it has no steps at all. -/
theorem deterministic_empty : Deterministic (⟨[]⟩ : RewriteSystem α) := by
  intro a b c hb _
  cases hb with
  | intro _ _ _ _ hr => cases hr

end StringRewriting
end GroupApproximation
