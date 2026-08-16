import GroupApproximation.Computability.OperatorMFMarkovAtCodes

/-!
# String rewriting systems

This file is the base of the only chain that can retire the development's last
literature input.  `cor:undecidable` rests on Adian--Rabin, Adian--Rabin rests
on a finitely presented group with undecidable word problem, and every route to
such a group runs through a *semi-Thue system*: a finite set of string
rewriting rules, simulating a machine, presenting a monoid whose word problem
is the machine's halting problem.  Boone--Britton then lifts the monoid to a
group through a tower of HNN extensions.

This file does the first step: rewriting systems, the derivability relation
they generate, and the closure properties that every simulation argument
downstream consumes.  It deliberately depends on nothing beyond lists and
`Relation`, so it cannot be destabilized by what is or is not in the built
`Mathlib` closure.

## What is here, and what is not

Here: the one-step relation, the fact that it is closed under context by
construction, and the proof that its equivalence closure is a *congruence* --
compatible with concatenation on both sides, and multiplicative in both
arguments at once.  That last fact is what lets a derivation be assembled from
derivations of its pieces, which is how every machine-simulation argument is
organized.

Not here: the simulation itself.  Encoding a Turing machine so that
derivability between configuration words is equivalent to halting requires
showing that rewriting is essentially deterministic on words carrying exactly
one state letter, and that is the substantial part of Post's theorem.  Nothing
in this file asserts it.
-/

namespace GroupApproximation
namespace StringRewriting

variable {α : Type*}

/-- A finite string rewriting system: a list of rules, each a pair of words. -/
structure RewriteSystem (α : Type*) where
  /-- The rules, as (left-hand side, right-hand side) pairs. -/
  rules : List (List α × List α)

/-- One rewriting step: replace an occurrence of a left-hand side by the
corresponding right-hand side, anywhere in the word. -/
inductive Step (R : RewriteSystem α) : List α → List α → Prop where
  | intro (u v l r : List α) (h : (l, r) ∈ R.rules) :
      Step R (u ++ l ++ v) (u ++ r ++ v)

/-- Derivability: a finite chain of rewriting steps, each in either direction.
This is exactly equality in the monoid presented by the system. -/
abbrev Derives (R : RewriteSystem α) : List α → List α → Prop :=
  Relation.EqvGen (Step R)

/-! ## Closure under context -/

/-- A rewriting step survives being placed in a larger context.  This holds by
construction: the rule already fires inside an arbitrary context, and enlarging
the context only re-associates the concatenation. -/
theorem Step.context {R : RewriteSystem α} {a b : List α} (h : Step R a b)
    (u v : List α) : Step R (u ++ a ++ v) (u ++ b ++ v) := by
  cases h with
  | intro u' v' l r hr =>
    have hleft : u ++ (u' ++ l ++ v') ++ v = (u ++ u') ++ l ++ (v' ++ v) := by
      simp [List.append_assoc]
    have hright : u ++ (u' ++ r ++ v') ++ v = (u ++ u') ++ r ++ (v' ++ v) := by
      simp [List.append_assoc]
    rw [hleft, hright]
    exact Step.intro (u ++ u') (v' ++ v) l r hr

/-- Derivability survives being placed in a larger context. -/
theorem Derives.context {R : RewriteSystem α} {a b : List α}
    (h : Derives R a b) (u v : List α) :
    Derives R (u ++ a ++ v) (u ++ b ++ v) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (hxy.context u v)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ihxy ihyz => exact Relation.EqvGen.trans _ _ _ ihxy ihyz

/-- Derivability is compatible with concatenation on the right. -/
theorem Derives.appendRight {R : RewriteSystem α} {a b : List α}
    (h : Derives R a b) (v : List α) : Derives R (a ++ v) (b ++ v) := by
  have := h.context [] v
  simpa using this

/-- Derivability is compatible with concatenation on the left. -/
theorem Derives.appendLeft {R : RewriteSystem α} {a b : List α}
    (h : Derives R a b) (u : List α) : Derives R (u ++ a) (u ++ b) := by
  have := h.context u []
  simpa using this

/-- **Derivability is a congruence.**  Two derivations can be run in parallel
on the two halves of a concatenation.  This is the form every simulation
argument uses: a derivation of a compound word is assembled from derivations of
its pieces. -/
theorem Derives.append {R : RewriteSystem α} {a b c d : List α}
    (hab : Derives R a b) (hcd : Derives R c d) :
    Derives R (a ++ c) (b ++ d) :=
  Relation.EqvGen.trans _ _ _ (hab.appendRight c) (hcd.appendLeft b)

/-! ## Elementary consequences -/

/-- A single rule is derivable in any context. -/
theorem derives_of_mem_rules {R : RewriteSystem α} {l r : List α}
    (h : (l, r) ∈ R.rules) (u v : List α) :
    Derives R (u ++ l ++ v) (u ++ r ++ v) :=
  Relation.EqvGen.rel _ _ (Step.intro u v l r h)

/-- Derivability is reflexive. -/
theorem Derives.refl {R : RewriteSystem α} (a : List α) : Derives R a a :=
  Relation.EqvGen.refl a

/-- Derivability is symmetric. -/
theorem Derives.symm {R : RewriteSystem α} {a b : List α} (h : Derives R a b) :
    Derives R b a :=
  Relation.EqvGen.symm _ _ h

/-- Derivability is transitive. -/
theorem Derives.trans {R : RewriteSystem α} {a b c : List α}
    (hab : Derives R a b) (hbc : Derives R b c) : Derives R a c :=
  Relation.EqvGen.trans _ _ _ hab hbc

/-- The system with no rules derives nothing beyond equality: the base case
that keeps the definitions honest. -/
theorem derives_empty_iff {a b : List α} :
    Derives (⟨[]⟩ : RewriteSystem α) a b ↔ a = b := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => cases hxy with | intro _ _ _ _ hr => cases hr
    | refl x => rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  · rintro rfl
    exact Relation.EqvGen.refl a

end StringRewriting
end GroupApproximation
