import GroupApproximation.Computability.StringRewriting

/-!
# The monoid presented by a string rewriting system

`Computability.StringRewriting` produced the derivability relation of a
semi-Thue system and proved it is a congruence.  This file cashes that in: the
quotient of words by derivability is a monoid, concatenation descends to it,
and its word problem *is* derivability.

The construction is done by hand rather than through a general congruence API,
for the same reason `StringRewriting` was: the chain toward Novikov--Boone has
to rest on the narrowest possible base, and the only inputs used here are the
three closure properties already proved.  In particular `Derives.append` is
exactly what makes concatenation well defined on the quotient --- the
congruence property is not a convenience, it is the reason the monoid exists.

## Where this sits

The point of the monoid is that its word problem is a *decision problem about
strings*, so it can be compared with machine halting.  Post's theorem says
some finite system has undecidable word problem; Boone--Britton then lifts
that monoid to a finitely presented group.  Neither is asserted here.  What is
here is the object those theorems talk about, together with the fact that
asking about equality in it is the same as asking about derivability.
-/

namespace GroupApproximation
namespace StringRewriting

variable {α : Type*}

/-- Derivability as a setoid on words: reflexive, symmetric and transitive by
`Relation.EqvGen`. -/
def setoid (R : RewriteSystem α) : Setoid (List α) where
  r := Derives R
  iseqv := ⟨Derives.refl, Derives.symm, Derives.trans⟩

/-- The monoid presented by a string rewriting system. -/
def RewriteMonoid (R : RewriteSystem α) : Type _ := Quotient (setoid R)

/-- A word, read in the presented monoid. -/
def mk (R : RewriteSystem α) (a : List α) : RewriteMonoid R :=
  Quotient.mk (setoid R) a

theorem mk_eq_mk_iff {R : RewriteSystem α} {a b : List α} :
    mk R a = mk R b ↔ Derives R a b :=
  Quotient.eq

/-- Concatenation descends to the quotient precisely because derivability is a
congruence. -/
instance monoid (R : RewriteSystem α) : Monoid (RewriteMonoid R) where
  mul x y :=
    Quotient.liftOn₂ x y (fun a b ↦ mk R (a ++ b))
      (fun _ _ _ _ h₁ h₂ ↦ Quotient.sound (h₁.append h₂))
  one := mk R []
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact congrArg (mk R) (List.append_assoc a b c)
  one_mul := by
    rintro ⟨a⟩
    exact congrArg (mk R) (List.nil_append a)
  mul_one := by
    rintro ⟨a⟩
    exact congrArg (mk R) (List.append_nil a)

@[simp] theorem mk_append (R : RewriteSystem α) (a b : List α) :
    mk R (a ++ b) = mk R a * mk R b := rfl

@[simp] theorem mk_nil (R : RewriteSystem α) : mk R [] = 1 := rfl

/-- Every element of the presented monoid is a word. -/
theorem mk_surjective (R : RewriteSystem α) : Function.Surjective (mk R) := by
  rintro ⟨a⟩
  exact ⟨a, rfl⟩

/-! ## The word problem -/

/-- **The word problem of a rewriting system is its derivability relation.**
This is the statement that makes the monoid usable as a decision problem: an
algorithm deciding equality in `RewriteMonoid R` is an algorithm deciding
derivability, and conversely. -/
theorem wordProblem_iff_derives {R : RewriteSystem α} (a b : List α) :
    mk R a = mk R b ↔ Derives R a b :=
  mk_eq_mk_iff

/-- The monoid presented by the empty system is free: nothing is identified.
This is the sanity check that the quotient has not collapsed. -/
theorem mk_injective_empty : Function.Injective (mk (⟨[]⟩ : RewriteSystem α)) := by
  intro a b hab
  exact derives_empty_iff.mp (mk_eq_mk_iff.mp hab)

end StringRewriting
end GroupApproximation
