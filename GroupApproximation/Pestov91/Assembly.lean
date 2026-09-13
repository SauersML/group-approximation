import GroupApproximation.Pestov91.Centre
import GroupApproximation.Pestov91.Kazhdan
import GroupApproximation.Sofic.LEF
import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Pestov Open Question 9.1: assembling the witness

Pestov's Open Question 9.1 (arXiv:0804.3968, Section 9, p. 21) asks whether an
infinite simple group with Kazhdan's property `(T)` can be hyperlinear
(sofic).  The witness is `S = EL₃(A)/Z(EL₃(A))` for the crossed product
`A = LC(X, 𝔽_q) ⋊ ℤ` of an infinite minimal subshift `X`.  This module puts
its properties together into the development endpoint that
`Palomar/Pestov91Solution.lean` consumes.

`exists_infinite_simple_kazhdan_lef_of` takes one hypothesis per ingredient
that is specific to the ring:

* `IsFinitelyGeneratedRing A`, which is all that property `(T)` needs:
  `elementaryModCentre_hasKazhdanPropertyT` in
  `GroupApproximation/Pestov91/Kazhdan.lean` proves `(T)` for `EL_n(A)/Z` for
  every finitely generated `A` and `n ≥ 3`, so `(T)` is not a hypothesis here;
* `Infinite A`, from which `elementaryModCentre_infinite` in
  `GroupApproximation/Pestov91/Centre.lean` makes `S` infinite: distinct
  off-diagonal entries give distinct cosets of the centre;
* `IsSimpleGroup S`;
* `IsLEF S`.  Soficity and hyperlinearity follow from it
  (`isSofic_of_isLEF`, `isHyperlinear_of_isSofic`), and the Solution makes that
  translation.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation

namespace Pestov91

/-- **The assembly.**  For an infinite finitely generated unital ring `A`, the
group `EL₃(A)/Z(EL₃(A))` is an infinite simple LEF group with property `(T)` as
soon as it is simple and LEF: it is infinite and has property `(T)` for every
such `A`. -/
theorem exists_infinite_simple_kazhdan_lef_of {A : Type} [Ring A] [Infinite A]
    (hA : IsFinitelyGeneratedRing A)
    (hsimple : IsSimpleGroup
      (↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A)))
    (hlef : IsLEF
      (↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A))) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E :=
  ⟨↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A),
    inferInstance, elementaryModCentre_infinite (0 : Fin 3) 1 (by decide), hsimple,
    elementaryModCentre_hasKazhdanPropertyT hA le_rfl, hlef⟩

end Pestov91

end GroupApproximation
