import GroupApproximation.Computability.RewriteInvariants

/-!
# Confluence and normal forms

`Computability.RewriteInvariants` gave the tools that confine a derivation.
This file gives the tool that *straightens* one.

Derivability is the equivalence closure of rewriting: a derivation is a zigzag,
stepping forwards and backwards arbitrarily.  Every simulation argument needs
to replace such a zigzag by something directed, because a machine only runs
forwards.  Confluence is what makes that possible, and the statement that it
does is the Church--Rosser property:

> in a confluent system, two words are derivable from one another exactly when
> they reduce to a common word.

`derives_iff_join` is that theorem.  Its corollary `eq_of_derives_of_normalForm`
is the form used in practice: in a confluent system, two *distinct* normal
forms are never derivable from one another.  That is how a simulation proves a
negative --- that a machine does not halt, that two configurations are
unrelated --- without searching the derivation space.

The proof of the forward direction is the standard induction over the
equivalence closure, and the `trans` case is the only one that uses
confluence: two joins meeting at a common middle word are merged by joining
their two witnesses.
-/

namespace GroupApproximation
namespace StringRewriting

variable {α : Type*}

/-! ## Directed reduction -/

/-- Directed reduction: finitely many rewriting steps, all forwards. -/
abbrev Reduces (R : RewriteSystem α) : List α → List α → Prop :=
  Relation.ReflTransGen (Step R)

/-- A reduction is in particular a derivation. -/
theorem Reduces.derives {R : RewriteSystem α} {a b : List α}
    (h : Reduces R a b) : Derives R a b := by
  induction h with
  | refl => exact Derives.refl a
  | tail _ hstep ih => exact ih.trans (Relation.EqvGen.rel _ _ hstep)

/-- A system is confluent when any two reductions out of a word can be
completed to a common word. -/
def Confluent (R : RewriteSystem α) : Prop :=
  ∀ a b c, Reduces R a b → Reduces R a c → ∃ d, Reduces R b d ∧ Reduces R c d

/-! ## Church--Rosser -/

/-- **Church--Rosser.**  In a confluent system a zigzag can be straightened:
two words are derivable from one another exactly when they reduce to a common
word.  This is what lets a simulation argument, which must reason about a
machine running forwards, handle a derivation that runs in both directions. -/
theorem derives_iff_join {R : RewriteSystem α} (hR : Confluent R) (a b : List α) :
    Derives R a b ↔ ∃ c, Reduces R a c ∧ Reduces R b c := by
  constructor
  · intro h
    induction h with
    | rel x y hxy =>
      exact ⟨y, Relation.ReflTransGen.single hxy, Relation.ReflTransGen.refl⟩
    | refl x =>
      exact ⟨x, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | symm x y _ ih =>
      obtain ⟨c, h₁, h₂⟩ := ih
      exact ⟨c, h₂, h₁⟩
    | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨d, hxd, hyd⟩ := ih₁
      obtain ⟨e, hye, hze⟩ := ih₂
      obtain ⟨f, hdf, hef⟩ := hR y d e hyd hye
      exact ⟨f, hxd.trans hdf, hze.trans hef⟩
  · rintro ⟨c, hac, hbc⟩
    exact hac.derives.trans hbc.derives.symm

/-! ## Normal forms -/

/-- A word is in normal form when no rule applies to it. -/
def NormalForm (R : RewriteSystem α) (a : List α) : Prop := ∀ b, ¬ Step R a b

/-- A reduction out of a normal form goes nowhere. -/
theorem eq_of_reduces_of_normalForm {R : RewriteSystem α} {a b : List α}
    (ha : NormalForm R a) (h : Reduces R a b) : a = b := by
  rcases Relation.ReflTransGen.cases_head h with h' | ⟨d, hd, _⟩
  · exact h'
  · exact absurd hd (ha d)

/-- **Distinct normal forms are not derivable from one another.**  This is the
separation tool: in a confluent system, to show two words are unrelated it is
enough to reduce each to a normal form and see that the normal forms differ ---
no search over derivations is needed. -/
theorem eq_of_derives_of_normalForm {R : RewriteSystem α} (hR : Confluent R)
    {a b : List α} (ha : NormalForm R a) (hb : NormalForm R b)
    (h : Derives R a b) : a = b := by
  obtain ⟨c, hac, hbc⟩ := (derives_iff_join hR a b).mp h
  have h₁ : a = c := eq_of_reduces_of_normalForm ha hac
  have h₂ : b = c := eq_of_reduces_of_normalForm hb hbc
  exact h₁.trans h₂.symm

/-- The same statement in the presented monoid: distinct normal forms stay
distinct after passing to the quotient. -/
theorem mk_ne_mk_of_normalForm {R : RewriteSystem α} (hR : Confluent R)
    {a b : List α} (ha : NormalForm R a) (hb : NormalForm R b)
    (hab : a ≠ b) : mk R a ≠ mk R b := by
  intro h
  exact hab (eq_of_derives_of_normalForm hR ha hb (mk_eq_mk_iff.mp h))

/-- Every word is in normal form for the empty system, so the empty system is
trivially confluent --- the base case that keeps the definitions honest. -/
theorem confluent_empty : Confluent (⟨[]⟩ : RewriteSystem α) := by
  intro a b c hab hac
  have hnf : NormalForm (⟨[]⟩ : RewriteSystem α) a := by
    intro y hy
    cases hy with
    | intro _ _ _ _ hr => cases hr
  have hb : a = b := eq_of_reduces_of_normalForm hnf hab
  have hc : a = c := eq_of_reduces_of_normalForm hnf hac
  subst hb
  subst hc
  exact ⟨a, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

end StringRewriting
end GroupApproximation
