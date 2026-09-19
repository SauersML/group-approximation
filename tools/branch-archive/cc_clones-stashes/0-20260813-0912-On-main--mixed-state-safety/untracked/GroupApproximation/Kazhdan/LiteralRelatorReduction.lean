import Mathlib.GroupTheory.PresentedGroup

/-!
# Proof-carrying reductions by presentation relators

This file provides a small, generic certificate language for exact word
equalities in a presented group.  A certificate atom is a conjugate of a
defining relator or its inverse.  A reduction records, in the free group,
that `lhs * rhs⁻¹` is a finite product of such atoms.  The soundness theorem
then turns the certificate into equality after `PresentedGroup.mk`.

The construction deliberately performs no word search and chooses no normal
form.  A solver may emit the finite data and a separate exact checker may
prove the free-group equality appearing in `Reduction.word_eq`.
-/

namespace GroupApproximation
namespace LiteralRelatorReduction

universe u

variable {α : Type u}

/-- One proof-carrying use of a defining relator.  If `inverted` is true, the
inverse relator is used. -/
structure Atom (R : Finset (FreeGroup α)) where
  conjugator : FreeGroup α
  relator : FreeGroup α
  relator_mem : relator ∈ R
  inverted : Bool

/-- The signed relator selected by an atom. -/
def Atom.signedRelator {R : Finset (FreeGroup α)} (a : Atom R) :
    FreeGroup α :=
  if a.inverted then a.relator⁻¹ else a.relator

/-- The free-group word represented by one certificate atom. -/
def Atom.word {R : Finset (FreeGroup α)} (a : Atom R) : FreeGroup α :=
  a.conjugator * a.signedRelator * a.conjugator⁻¹

/-- The finite product represented by a list of certificate atoms. -/
def certificateWord {R : Finset (FreeGroup α)} (atoms : List (Atom R)) :
    FreeGroup α :=
  (atoms.map Atom.word).prod

/-- Any homomorphism killing the defining relators kills a certificate atom. -/
theorem map_atom_word_eq_one {R : Finset (FreeGroup α)}
    {H : Type*} [Group H] (φ : FreeGroup α →* H)
    (hR : ∀ r ∈ R, φ r = 1) (a : Atom R) :
    φ a.word = 1 := by
  have hr : φ a.relator = 1 := hR a.relator a.relator_mem
  by_cases hinv : a.inverted
  · simp [Atom.word, Atom.signedRelator, hinv, hr]
  · simp [Atom.word, Atom.signedRelator, hinv, hr]

/-- Any homomorphism killing the defining relators kills the product encoded
by a certificate. -/
theorem map_certificateWord_eq_one {R : Finset (FreeGroup α)}
    {H : Type*} [Group H] (φ : FreeGroup α →* H)
    (hR : ∀ r ∈ R, φ r = 1) (atoms : List (Atom R)) :
    φ (certificateWord atoms) = 1 := by
  induction atoms with
  | nil => simp [certificateWord]
  | cons a atoms ih =>
      change φ (a.word * (atoms.map Atom.word).prod) = 1
      rw [map_mul, map_atom_word_eq_one φ hR a]
      change φ (atoms.map Atom.word).prod = 1 at ih
      rw [ih, mul_one]

/-- Every certificate product is trivial in the group presented by `R`. -/
theorem presentedGroup_mk_certificateWord_eq_one
    {R : Finset (FreeGroup α)} (atoms : List (Atom R)) :
    PresentedGroup.mk (R : Set (FreeGroup α)) (certificateWord atoms) = 1 := by
  apply map_certificateWord_eq_one
  intro r hr
  exact PresentedGroup.one_of_mem hr

/-- A proof-carrying reduction from `lhs` to `rhs`.  The only trusted
mathematical payload is the explicit free-group equality `word_eq`; all uses
of presentation relations are listed in `atoms`. -/
structure Reduction (R : Finset (FreeGroup α))
    (lhs rhs : FreeGroup α) where
  atoms : List (Atom R)
  word_eq : lhs * rhs⁻¹ = certificateWord atoms

/-- Soundness of a proof-carrying reduction in the presented group. -/
theorem Reduction.sound {R : Finset (FreeGroup α)}
    {lhs rhs : FreeGroup α} (d : Reduction R lhs rhs) :
    PresentedGroup.mk (R : Set (FreeGroup α)) lhs =
      PresentedGroup.mk (R : Set (FreeGroup α)) rhs := by
  apply eq_of_mul_inv_eq_one
  have hcert := presentedGroup_mk_certificateWord_eq_one d.atoms
  have hword :
      PresentedGroup.mk (R : Set (FreeGroup α)) (lhs * rhs⁻¹) = 1 := by
    rw [d.word_eq]
    exact hcert
  simpa using hword

/-- An equality already valid in the free group gives an empty reduction. -/
def Reduction.ofEq {R : Finset (FreeGroup α)}
    {lhs rhs : FreeGroup α} (h : lhs = rhs) : Reduction R lhs rhs where
  atoms := []
  word_eq := by simp [h, certificateWord]

/-- A certificate that a word is trivial in the presented group. -/
abbrev Trivialization (R : Finset (FreeGroup α)) (word : FreeGroup α) :=
  Reduction R word 1

/-- Soundness in the common special case of a word trivialization. -/
theorem Trivialization.sound {R : Finset (FreeGroup α)}
    {word : FreeGroup α} (d : Trivialization R word) :
    PresentedGroup.mk (R : Set (FreeGroup α)) word = 1 := by
  simpa using Reduction.sound d

end LiteralRelatorReduction
end GroupApproximation
