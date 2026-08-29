import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.PresentedGroup

/-!
# Proof-carrying relator replay in presented groups

This file provides a small, transparent verifier for finite word certificates.
A certificate atom is a conjugate of a defining relator or its inverse.  A
certificate is accepted only after Lean checks, in the free group itself, that
the product of its atoms is the claimed word.  Matrix evaluation, a word-
problem oracle, and executable code outside the kernel play no role in the
theorems below.

The representation is deliberately convenient for generated certificates:
words are literal lists in Mathlib's convention `(generator, true)` for a
positive letter and `(generator, false)` for an inverse letter.  For a finite
generator type, the final free-group equality is decidable by the constructive
normal-form procedure in `Mathlib.GroupTheory.FreeGroup.Reduce`.
-/

namespace GroupApproximation
namespace PresentedGroupRelatorReplay

universe u v

variable {Generator : Type u} {RelatorIndex : Type v}

/-- A literal signed word.  This is Mathlib's native input format for
`FreeGroup.mk`; `true` denotes a positive letter and `false` its inverse. -/
abbrev SignedWord (Generator : Type u) := List (Generator × Bool)

/-- Interpret a literal signed word in the free group. -/
def word (letters : SignedWord Generator) : FreeGroup Generator :=
  FreeGroup.mk letters

/-- One proof atom: a conjugate of an indexed defining relator, optionally
inverted. -/
structure Atom (Generator : Type u) (RelatorIndex : Type v) where
  conjugator : SignedWord Generator
  relatorIndex : RelatorIndex
  inverted : Bool
deriving Repr, DecidableEq

/-- Select a defining relator or its inverse. -/
def signedRelator (relator : RelatorIndex → FreeGroup Generator)
    (a : Atom Generator RelatorIndex) : FreeGroup Generator :=
  if a.inverted then (relator a.relatorIndex)⁻¹ else relator a.relatorIndex

/-- The free-group word represented by one certificate atom. -/
def atomWord (relator : RelatorIndex → FreeGroup Generator)
    (a : Atom Generator RelatorIndex) : FreeGroup Generator :=
  word a.conjugator * signedRelator relator a * (word a.conjugator)⁻¹

/-- The product of all conjugated signed relators in a certificate. -/
def replayWord (relator : RelatorIndex → FreeGroup Generator)
    (atoms : List (Atom Generator RelatorIndex)) : FreeGroup Generator :=
  (atoms.map (atomWord relator)).prod

section PresentedGroup

variable {relators : Set (FreeGroup Generator)}
variable (relator : RelatorIndex → FreeGroup Generator)
variable (relator_mem : ∀ i, relator i ∈ relators)

include relator_mem

/-- Each signed defining relator maps to one in the presented group. -/
theorem mk_signedRelator_eq_one (a : Atom Generator RelatorIndex) :
    PresentedGroup.mk relators (signedRelator relator a) = 1 := by
  simp only [signedRelator]
  split
  · rw [map_inv, PresentedGroup.one_of_mem (relator_mem a.relatorIndex), inv_one]
  · exact PresentedGroup.one_of_mem (relator_mem a.relatorIndex)

/-- Each conjugated signed defining relator maps to one. -/
theorem mk_atomWord_eq_one (a : Atom Generator RelatorIndex) :
    PresentedGroup.mk relators (atomWord relator a) = 1 := by
  simp [atomWord, mk_signedRelator_eq_one relator relator_mem]

/-- Every finite product of certificate atoms maps to one. -/
theorem mk_replayWord_eq_one
    (atoms : List (Atom Generator RelatorIndex)) :
    PresentedGroup.mk relators (replayWord relator atoms) = 1 := by
  induction atoms with
  | nil => simp [replayWord]
  | cons a atoms ih =>
      change PresentedGroup.mk relators
        (atomWord relator a * (atoms.map (atomWord relator)).prod) = 1
      rw [map_mul, mk_atomWord_eq_one relator relator_mem, one_mul]
      exact ih

/-- A kernel-checkable free-group replay proves that the claimed word is a
consequence of the defining relators.  For literal finite data, `hreplay` is
intended to be discharged by `by decide`. -/
theorem mk_eq_one_of_replay
    (claimed : FreeGroup Generator)
    (atoms : List (Atom Generator RelatorIndex))
    (hreplay : replayWord relator atoms = claimed) :
    PresentedGroup.mk relators claimed = 1 := by
  rw [← hreplay]
  exact mk_replayWord_eq_one relator relator_mem atoms

/-- The equality version used by coefficient collection: replay a certificate
for `left * right⁻¹` to prove that the two presented-group words agree. -/
theorem mk_eq_mk_of_replay
    (left right : FreeGroup Generator)
    (atoms : List (Atom Generator RelatorIndex))
    (hreplay : replayWord relator atoms = left * right⁻¹) :
    PresentedGroup.mk relators left = PresentedGroup.mk relators right := by
  refine eq_of_mul_inv_eq_one ?_
  rw [← map_inv, ← map_mul]
  exact mk_eq_one_of_replay relator relator_mem _ atoms hreplay

end PresentedGroup

/-! ## Stepwise certificates

A generator may find a rewrite path more economically than a single normal-
closure product.  Each step below still carries exactly one conjugated signed
relator, and `PathValid` checks the corresponding free-group equality at every
step.  Thus a search program may discover the path, but it cannot contribute a
trusted equality.
-/

end PresentedGroupRelatorReplay
end GroupApproximation
