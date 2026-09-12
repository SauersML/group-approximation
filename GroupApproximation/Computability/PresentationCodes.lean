import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Computability.MarkovReductionInterface

/-!
# A recursive coding of finite presentations

`Computability.MarkovReductionInterface` deliberately leaves the syntax and
semantics of presentation codes as parameters, and says so:

> The syntax and semantics of codes are deliberately parameters: different
> exact encodings can share the same reduction theorem.

and

> This structure only interprets codes; computability of syntactic operations
> belongs in a specific coding implementation.

This file is that specific coding implementation.  It fixes one concrete
recursive datatype of finite presentations, interprets it, and discharges the
two structural obligations an Adian--Rabin reduction has to meet before any
group theory is done:

* the code type is `Primcodable`, so "computable transformation of codes" is a
  meaningful predicate; and
* every code names a genuinely *finitely presented* group, which is what
  `FinitePresentationSemantics` demands.

## What this does and does not close

`MarkovMFConsequences.AdianRabinReduction` has four fields.  This file
inhabits the ambient data for two of them --- the `Primcodable` code type and
the `FinitePresentationSemantics` --- and leaves the other two open: the
computable `transform`, and its correctness equivalence.  Those are the
Adian--Rabin construction proper, and they need a finitely presented group
with undecidable word problem (Novikov--Boone) together with HNN normal-form
machinery, neither of which is available.

So this is scaffolding, not the theorem.  It is worth having separately
because it is the half that is *not* research-scale, and because until a code
type exists the phrase "computable map on finite presentations" has no
referent in the development at all.

## Design

A code is a pair: a generator count and a list of relator words, each word a
list of signed generator indices.  Two totality choices keep interpretation a
plain function rather than a partial one:

* the generator count is stored offset by one, so every code names a nonempty
  alphabet; and
* a letter index is read modulo the alphabet size, so every list of naturals
  denotes a word.

Both choices cost nothing: the coding is meant to be *onto* finite
presentations up to isomorphism, not injective, and every finite presentation
is named by some code.
-/

namespace GroupApproximation
namespace PresentationCodes

open MarkovMFConsequences

/-- A code for a finite presentation: a generator count (stored offset by one)
together with a finite list of relator words, each a list of signed generator
indices. -/
abbrev PresentationCode : Type := ℕ × List (List (ℕ × Bool))

/-- Codes are a recursive datatype, so "computable transformation of finite
presentations" is a meaningful predicate. -/
example : Primcodable PresentationCode := inferInstance

/-- The alphabet size named by a code.  Reducible on purpose: the alphabet
appears inside the *type* `Fin (genCount c)`, so every lemma about a code built
from an explicit pair needs `genCount` to reduce, or its statement will not
even typecheck against `Fin (m + 1)`. -/
abbrev genCount (c : PresentationCode) : ℕ := c.1 + 1

theorem genCount_pos (c : PresentationCode) : 0 < genCount c := Nat.succ_pos _

/-- Letters are interpreted totally, by reduction modulo the alphabet size. -/
def letterOf (c : PresentationCode) (i : ℕ) : Fin (genCount c) :=
  ⟨i % genCount c, Nat.mod_lt _ (genCount_pos c)⟩

/-- A coded word, read in the free group on the alphabet. -/
def wordOf (c : PresentationCode) (w : List (ℕ × Bool)) :
    FreeGroup (Fin (genCount c)) :=
  FreeGroup.mk (w.map fun p ↦ (letterOf c p.1, p.2))

/-- The finite relator set named by a code. -/
def relatorFinset (c : PresentationCode) :
    Finset (FreeGroup (Fin (genCount c))) :=
  (c.2.map (wordOf c)).toFinset

/-- The group presented by a code.  This is an `abbrev` on purpose: the group
and finite-presentation instances of `PresentedGroup` have to transfer through
it, exactly as they do for the manuscript's own presented groups. -/
abbrev Carrier (c : PresentationCode) : Type :=
  PresentedGroup
    ((relatorFinset c : Finset (FreeGroup (Fin (genCount c)))) :
      Set (FreeGroup (Fin (genCount c))))

/-- Every coded group is finitely presented: the alphabet is a `Fin` type and
the relator set is a `Finset`. -/
example (c : PresentationCode) : Group.IsFinitelyPresented (Carrier c) :=
  inferInstance

/-- **The coding implementation `MarkovMFConsequences` asks for.**  Together
with the `Primcodable` instance above, this is the ambient data of an
Adian--Rabin reduction; the transformation itself and its correctness are not
supplied here. -/
def semantics : FinitePresentationSemantics PresentationCode where
  Carrier := Carrier
  group := fun _ ↦ inferInstance
  finitelyPresented := fun _ ↦ inferInstance

/-- Unfolding the recognition predicate at this coding: a code is a positive
instance exactly when the group it presents is operator-MF. -/
theorem operatorMFProperty_semantics (c : PresentationCode) :
    operatorMFProperty semantics c ↔ IsOperatorMF (Carrier c) :=
  Iff.rfl

end PresentationCodes
end GroupApproximation
