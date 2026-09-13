import GroupApproximation.SurjunctiveNonsofic.LaurentPairKazhdan
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Property `(T)` for the Pestov 9.1 witness, and its quotient by the centre

Pestov's Open Question 9.1 (*Hyperlinear and sofic groups: a brief guide*,
arXiv:0804.3968v8, p. 21) asks whether an infinite simple group with Kazhdan's
property `(T)` can be hyperlinear.  The witness of this development is

  `S = EL₃(R) / Z(EL₃(R))`,  with `R = LC(X, 𝔽_q) ⋊ ℤ` for an infinite minimal
  subshift `X`.

This module supplies the property-`(T)` half of that witness.  It carries no
hypothesis: both steps are theorems of this repository.

1. **`EL_n(A)` has `(T)`** for every finitely generated unital ring `A` and
   every rank `n ≥ 3`.  This is the Ershov--Jaikin-Zapirain theorem, proved
   outright here as
   `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`.
   Its printed finite-generation hypothesis is `IsFinitelyGeneratedRing`, and
   its coefficient ring ranges over `Type` (universe `0`), so the witness ring
   has to be produced there.

2. **`(T)` passes to quotients.**  A representation of `G ⧸ N` with a
   `(Q, ε)`-almost invariant unit vector pulls back along `QuotientGroup.mk'`
   to a representation of `G` that is almost invariant for a preimage of the
   control set; a nonzero `G`-invariant vector for the pullback is
   `G ⧸ N`-invariant because `mk'` is surjective.  That pullback argument is
   `HasKazhdanPropertyT.of_surjective`, already on main; `quotient` below is
   the quotient-group instance of it, and it is the general statement, not one
   tied to the centre.

The centre is normal, so the two steps compose: `elementaryModCentre` is
property `(T)` for `EL_n(A)/Z(EL_n(A))` over every finitely generated `A`.
Nothing here needs `A` to be simple, or `n` to be `3`.

The interface a peer lane consumes is `hasKazhdanPropertyT_of_surjective`,
which transports `(T)` from `EL_n(A)` onto *any* group carrying a surjection
from it: a lane that builds `S` as something other than the Lean quotient type
supplies its own surjection and needs nothing else from this module.
-/

namespace GroupApproximation

universe u v

namespace HasKazhdanPropertyT

/-- **Property `(T)` passes to quotient groups.**  The quotient map is
surjective, so this is the quotient-group instance of `of_surjective`. -/
theorem quotient {G : Type u} [Group G] (N : Subgroup G) [N.Normal]
    (hG : HasKazhdanPropertyT.{u, v} G) :
    HasKazhdanPropertyT.{u, v} (G ⧸ N) :=
  HasKazhdanPropertyT.of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) hG

/-- Property `(T)` passes to the quotient by the centre. -/
theorem quotientCenter {G : Type u} [Group G]
    (hG : HasKazhdanPropertyT.{u, v} G) :
    HasKazhdanPropertyT.{u, v} (G ⧸ Subgroup.center G) :=
  quotient (Subgroup.center G) hG

end HasKazhdanPropertyT

namespace Pestov91

/-- **`EL_n(A)` has property `(T)`** for every finitely generated unital ring
`A` and every rank `n ≥ 3`.  This is the Ershov--Jaikin-Zapirain theorem in
the form this repository proves it. -/
theorem elementary_hasKazhdanPropertyT {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A) {n : ℕ} (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin n) A) :=
  IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT
    A hA n hn

/-- **The interface for the witness group.**  Any group carrying a surjection
from `EL_n(A)` has property `(T)`, for `A` finitely generated and `n ≥ 3`.

A lane that realises `S = EL₃(R)/Z` as a group of its own -- rather than as
the Lean quotient type -- consumes this lemma with its own surjection and
needs nothing else from this module. -/
theorem hasKazhdanPropertyT_of_surjective {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A) {n : ℕ} (hn : 3 ≤ n)
    {S : Type} [Group S] (f : ↥(elementaryGroup (Fin n) A) →* S)
    (hf : Function.Surjective f) :
    HasKazhdanPropertyT.{0, 0} S :=
  HasKazhdanPropertyT.of_surjective f hf (elementary_hasKazhdanPropertyT hA hn)

/-- **`EL_n(A)/Z(EL_n(A))` has property `(T)`** for every finitely generated
unital ring `A` and every rank `n ≥ 3`.  This is the property-`(T)` half of
the Pestov 9.1 witness, before the witness ring is chosen. -/
theorem elementaryModCentre_hasKazhdanPropertyT {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A) {n : ℕ} (hn : 3 ≤ n) :
    HasKazhdanPropertyT.{0, 0}
      (↥(elementaryGroup (Fin n) A) ⧸
        Subgroup.center ↥(elementaryGroup (Fin n) A)) :=
  HasKazhdanPropertyT.quotientCenter (elementary_hasKazhdanPropertyT hA hn)

/-- The same statement for a normal subgroup of the centre that a lane may
prefer to name explicitly: any normal subgroup will do, the centre included. -/
theorem elementaryModNormal_hasKazhdanPropertyT {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A) {n : ℕ} (hn : 3 ≤ n)
    (N : Subgroup ↥(elementaryGroup (Fin n) A)) [N.Normal] :
    HasKazhdanPropertyT.{0, 0} (↥(elementaryGroup (Fin n) A) ⧸ N) :=
  HasKazhdanPropertyT.quotient N (elementary_hasKazhdanPropertyT hA hn)

/-! ### Calibration

`ℤ` is a finitely generated ring, so the statements above are not vacuous:
they have a concrete instance at the smallest coefficient ring.  `EL₃(ℤ)` is
`SL₃(ℤ)` and its quotient by the centre is `PSL₃(ℤ)`, the classical Kazhdan
group; the point of the line is only that the general theorem applies to a
ring that exists, with no hypothesis left over. -/

/-- Calibration at `A = ℤ`: `EL₃(ℤ)` has property `(T)`. -/
theorem intElementary_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0} ↥(elementaryGroup (Fin 3) ℤ) :=
  elementary_hasKazhdanPropertyT SurjunctiveNonsofic.isFinitelyGeneratedRing_int le_rfl

/-- Calibration at `A = ℤ`: `EL₃(ℤ)/Z(EL₃(ℤ))` has property `(T)`. -/
theorem intElementaryModCentre_hasKazhdanPropertyT :
    HasKazhdanPropertyT.{0, 0}
      (↥(elementaryGroup (Fin 3) ℤ) ⧸
        Subgroup.center ↥(elementaryGroup (Fin 3) ℤ)) :=
  elementaryModCentre_hasKazhdanPropertyT
    SurjunctiveNonsofic.isFinitelyGeneratedRing_int le_rfl

end Pestov91
end GroupApproximation
