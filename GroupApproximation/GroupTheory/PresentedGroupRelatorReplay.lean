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
  apply eq_of_mul_inv_eq_one
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

/-- One step of a proof-producing rewrite path. -/
structure Step (Generator : Type u) (RelatorIndex : Type v) where
  next : SignedWord Generator
  atom : Atom Generator RelatorIndex
deriving Repr, DecidableEq

/-- The endpoint obtained by following a list of rewrite steps. -/
def pathEndpoint (start : SignedWord Generator) :
    List (Step Generator RelatorIndex) → SignedWord Generator
  | [] => start
  | step :: steps => pathEndpoint step.next steps

/-- Every path step must exhibit the exact free-group quotient between its
current and next words as the stated relator atom. -/
def PathValid (relator : RelatorIndex → FreeGroup Generator) :
    SignedWord Generator → List (Step Generator RelatorIndex) → Prop
  | _, [] => True
  | current, step :: steps =>
      word current * (word step.next)⁻¹ = atomWord relator step.atom ∧
        PathValid relator step.next steps

section Stepwise

variable {relators : Set (FreeGroup Generator)}
variable (relator : RelatorIndex → FreeGroup Generator)
variable (relator_mem : ∀ i, relator i ∈ relators)

include relator_mem

private theorem mk_word_eq_mk_word_of_valid_step
    (current : SignedWord Generator)
    (step : Step Generator RelatorIndex)
    (hstep : word current * (word step.next)⁻¹ =
      atomWord relator step.atom) :
    PresentedGroup.mk relators (word current) =
      PresentedGroup.mk relators (word step.next) := by
  apply eq_of_mul_inv_eq_one
  rw [← map_inv, ← map_mul, hstep]
  exact mk_atomWord_eq_one relator relator_mem step.atom

/-- A valid stepwise replay proves equality of its start and computed endpoint
in the presented group. -/
theorem mk_word_eq_pathEndpoint
    (start : SignedWord Generator)
    (steps : List (Step Generator RelatorIndex))
    (hvalid : PathValid relator start steps) :
    PresentedGroup.mk relators (word start) =
      PresentedGroup.mk relators (word (pathEndpoint start steps)) := by
  induction steps generalizing start with
  | nil => rfl
  | cons step steps ih =>
      exact (mk_word_eq_mk_word_of_valid_step relator relator_mem start step
        hvalid.1).trans (ih step.next hvalid.2)

/-- A checked stepwise path ending at the requested literal word proves the
corresponding equality in the presented group. -/
theorem mk_word_eq_word_of_path
    (start finish : SignedWord Generator)
    (steps : List (Step Generator RelatorIndex))
    (hvalid : PathValid relator start steps)
    (hfinish : pathEndpoint start steps = finish) :
    PresentedGroup.mk relators (word start) =
      PresentedGroup.mk relators (word finish) := by
  subst finish
  exact mk_word_eq_pathEndpoint relator relator_mem start steps hvalid

end Stepwise

end PresentedGroupRelatorReplay
end GroupApproximation
