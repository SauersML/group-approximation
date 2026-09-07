import Mathlib.Data.Countable.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Countability of matrix rings and of unit groups

Three facts that every module needing "a countable ring has a countable general
linear group" has so far re-derived inline:

* `Countable Mˣ` from `Countable M`, because `Units.val` is injective;
* `Countable (Matrix (Fin n) (Fin n) A)` from `Countable A` — **not** found by
  instance search, because `Matrix` is a definition rather than a `Pi` type as
  far as instance resolution is concerned, so the `Pi.countable` instance never
  fires;
* the combination, `Countable (GL_n(A))`.

## Why this module exists

Before it, the tree proved these in at least five places, in four vocabularies:
`Leavitt/FamilyRankFour.lean` (`countable_units`, `matrixCountable`,
`unitsMatrixCountable`, `unitsCountable`), `Leavitt/RankTwoCompression.lean`
(inline `haveI`s through `Countable.of_equiv`),
`Manuscript/OneSidedMFRadical/LeavittMFQuotientGeneral.lean` (`countableAryMatrix`,
`countableAryGL`), `Manuscript/OneSidedMFRadical/MFQuotientUnits.lean` (an inline
`show ... ; infer_instance`), and `KOne/AlgebraicKOne.lean`.

`FamilyRankFour`'s version is the oldest and the most general, and it is
`private`, so nothing outside that file can use it; that is why each later
module wrote its own.  Its instances are also namespace-scoped and fixed at
`Type`.  This module is a leaf with two Mathlib imports and no repository
dependency, so any of those sites can adopt it without taking on weight.

## Theorems, not global instances

A global `Countable Mˣ` instance would fire on every unit group in the
development.  `FamilyRankFour` deliberately kept its versions namespace-scoped,
and that judgement is kept here: these are theorems, to be named at the point of
use, exactly as the existing call sites already name their local `haveI`s.
-/

namespace GroupApproximation
namespace CountableMatrixUnits

/-- Units of a countable monoid are countable: `Units.val` is injective. -/
theorem countable_units {M : Type*} [Monoid M] [Countable M] : Countable Mˣ :=
  Units.val_injective.countable

/-- A square matrix ring over a countable ring is countable.

Instance search does not find this on its own: `Matrix` is a definition, not a
`Pi` type as far as resolution is concerned, so `Pi.countable` never applies. -/
theorem countable_matrix {A : Type*} [Countable A] (n : ℕ) :
    Countable (Matrix (Fin n) (Fin n) A) :=
  inferInstanceAs (Countable (Fin n → Fin n → A))

/-- `GL_n(A)` is countable when `A` is. -/
theorem countable_matrix_units {A : Type*} [Semiring A] [Countable A] (n : ℕ) :
    Countable ((Matrix (Fin n) (Fin n) A)ˣ) :=
  haveI := countable_matrix (A := A) n
  countable_units

end CountableMatrixUnits
end GroupApproximation
