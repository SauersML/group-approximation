import GroupApproximation.Pestov91.Centre
import GroupApproximation.Pestov91.CentreSkew
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
* `IsSimpleGroup S`;
* `Infinite S`, which `elementaryModCentre_infinite` supplies for an infinite
  ring (`GroupApproximation/Pestov91/Centre.lean`), and
  `elementaryModCentre_crossedProduct_infinite` for the crossed product
  (`GroupApproximation/Pestov91/CentreSkew.lean`);
* `IsLEF S`.  Soficity and hyperlinearity follow from it
  (`isSofic_of_isLEF`, `isHyperlinear_of_isSofic`), and the Solution makes that
  translation.

`exists_infinite_simple_kazhdan_lef_of_crossedProduct` specialises to
`A = SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ)` for a nonempty
space `X`, a nontrivial ring `K` and any action of `ℤ`, and discharges
`Infinite S` there.  So for the witness only finite generation, simplicity and
LEF remain.

When the centre of `EL₃(A)` is trivial (the case `q = 2`), the witness can be
`EL₃(A)` itself: `exists_infinite_simple_kazhdan_lef_of_elementary` takes
simplicity and LEF of `EL₃(A)`, gets property `(T)` from
`elementary_hasKazhdanPropertyT`, and gets infiniteness by surjecting onto the
infinite quotient.  `isSimpleGroup_elementaryModCentre` passes simplicity from
`EL₃(A)` down to `EL₃(A)/Z(EL₃(A))` over any nontrivial ring.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation

namespace Pestov91

/-- **The assembly.**  For a finitely generated unital ring `A`, the group
`EL₃(A)/Z(EL₃(A))` is an infinite simple LEF group with property `(T)` as soon
as it is simple, infinite and LEF: property `(T)` holds for every such `A`. -/
theorem exists_infinite_simple_kazhdan_lef_of {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A)
    (hsimple : IsSimpleGroup
      (↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A)))
    (hinfinite : Infinite
      (↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A)))
    (hlef : IsLEF
      (↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A))) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E :=
  ⟨↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A),
    inferInstance, hinfinite, hsimple,
    elementaryModCentre_hasKazhdanPropertyT hA le_rfl, hlef⟩

/-- **The assembly for the crossed product.**  For a nonempty space `X`, a
nontrivial ring `K` and an action of `ℤ` on `LC(X, K)`, put
`A = LC(X, K) ⋊ ℤ`.  If `A` is finitely generated and `EL₃(A)/Z(EL₃(A))` is
simple and LEF, that group is an infinite simple LEF group with property `(T)`:
it is infinite by `elementaryModCentre_crossedProduct_infinite`. -/
theorem exists_infinite_simple_kazhdan_lef_of_crossedProduct {X K : Type}
    [TopologicalSpace X] [Nonempty X] [Ring K] [Nontrivial K]
    [MulSemiringAction (Multiplicative ℤ) (LocallyConstant X K)]
    (hA : IsFinitelyGeneratedRing (SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ)))
    (hsimple : IsSimpleGroup
      (↥(elementaryGroup (Fin 3) (SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ))) ⧸
        Subgroup.center
          ↥(elementaryGroup (Fin 3) (SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ)))))
    (hlef : IsLEF
      (↥(elementaryGroup (Fin 3) (SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ))) ⧸
        Subgroup.center
          ↥(elementaryGroup (Fin 3) (SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ))))) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E :=
  exists_infinite_simple_kazhdan_lef_of hA hsimple elementaryModCentre_crossedProduct_infinite hlef

/-- **The assembly with `EL₃(A)` as the witness.**  For a finitely generated
unital ring `A` whose quotient `EL₃(A)/Z(EL₃(A))` is infinite, the group
`EL₃(A)` is an infinite simple LEF group with property `(T)` as soon as it is
simple and LEF. -/
theorem exists_infinite_simple_kazhdan_lef_of_elementary {A : Type} [Ring A]
    (hA : IsFinitelyGeneratedRing A)
    (hsimple : IsSimpleGroup ↥(elementaryGroup (Fin 3) A))
    (hinfinite : Infinite
      (↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A)))
    (hlef : IsLEF ↥(elementaryGroup (Fin 3) A)) :
    ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧
      HasKazhdanPropertyT.{0, 0} E ∧ IsLEF E :=
  ⟨↥(elementaryGroup (Fin 3) A), inferInstance,
    Infinite.of_surjective ⇑(QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup (Fin 3) A)))
      (QuotientGroup.mk'_surjective _),
    hsimple, elementary_hasKazhdanPropertyT hA le_rfl, hlef⟩

/-- Simplicity of `EL₃(A)` passes to `EL₃(A)/Z(EL₃(A))` over every nontrivial
ring: the quotient map is surjective and the quotient is nontrivial. -/
theorem isSimpleGroup_elementaryModCentre {A : Type} [Ring A] [Nontrivial A]
    (hsimple : IsSimpleGroup ↥(elementaryGroup (Fin 3) A)) :
    IsSimpleGroup
      (↥(elementaryGroup (Fin 3) A) ⧸ Subgroup.center ↥(elementaryGroup (Fin 3) A)) :=
  haveI := elementaryModCentre_nontrivial (R := A) (0 : Fin 3) 1 (by decide)
  IsSimpleGroup.isSimpleGroup_of_surjective
    (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup (Fin 3) A)))
    (QuotientGroup.mk'_surjective _)

end Pestov91

end GroupApproximation
