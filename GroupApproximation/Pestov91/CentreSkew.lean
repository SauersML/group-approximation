import GroupApproximation.Pestov91.Centre
import Mathlib.Algebra.SkewMonoidAlgebra.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# `EL₃(R)/Z` is infinite for the crossed product `R = LC(X, K) ⋊ ℤ`

The witness ring for Pestov's Open Question 9.1 is the skew monoid algebra
`SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ)`.  This module removes the
`[Infinite R]` hypothesis of `elementaryModCentre_infinite`
(`GroupApproximation/Pestov91/Centre.lean`) for every such ring.

* `skewMonoidAlgebra_infinite`: a skew monoid algebra with nonzero coefficients over an
  infinite monoid is infinite, since `g ↦ single g b` is injective for `b ≠ 0`.
* `locallyConstant_nontrivial`: `LocallyConstant X K` is nontrivial for nonempty `X` and
  nontrivial `K`.
* `elementaryModCentre_crossedProduct_infinite`: `EL₃(LC(X, K) ⋊ ℤ)/Z` is infinite for every
  nonempty `X`, nontrivial `K` and every action of `ℤ`.  Neither minimality, freeness nor any
  property of the action is used.
-/

namespace GroupApproximation
namespace Pestov91

/-- A skew monoid algebra with a nonzero coefficient over an infinite monoid is infinite. -/
theorem skewMonoidAlgebra_infinite {k G : Type*} [AddMonoid k] [Nontrivial k] [Infinite G] :
    Infinite (SkewMonoidAlgebra k G) := by
  obtain ⟨b, hb⟩ := exists_ne (0 : k)
  exact Infinite.of_injective (fun g : G ↦ SkewMonoidAlgebra.single g b)
    fun _ _ h ↦ (SkewMonoidAlgebra.single_left_inj hb).mp h

/-- Locally constant functions on a nonempty space with values in a nontrivial `K` form a
nontrivial type: `0 ≠ 1`. -/
theorem locallyConstant_nontrivial {X K : Type*} [TopologicalSpace X] [Nonempty X]
    [MulZeroOneClass K] [Nontrivial K] : Nontrivial (LocallyConstant X K) :=
  nontrivial_of_ne 0 1 fun h ↦ by
    simpa using DFunLike.congr_fun h (Classical.arbitrary X)

/-- `EL₃(k ⋊ G)/Z` is infinite for a nontrivial ring `k` and an infinite monoid `G`, whatever
the action. -/
theorem elementaryModCentre_skewMonoidAlgebra_infinite {k G : Type*} [Ring k] [Nontrivial k]
    [Monoid G] [Infinite G] [MulSemiringAction G k] :
    Infinite (↥(elementaryGroup (Fin 3) (SkewMonoidAlgebra k G)) ⧸
      Subgroup.center ↥(elementaryGroup (Fin 3) (SkewMonoidAlgebra k G))) :=
  haveI : Infinite (SkewMonoidAlgebra k G) := skewMonoidAlgebra_infinite
  elementaryModCentre_infinite (0 : Fin 3) 1 (by decide)

/-- **`S` is infinite.**  For the crossed product `LC(X, K) ⋊ ℤ` of any nonempty space `X`, any
nontrivial ring `K` and any action of `ℤ`, the group `EL₃(R)/Z(EL₃(R))` is infinite. -/
theorem elementaryModCentre_crossedProduct_infinite {X K : Type*} [TopologicalSpace X]
    [Nonempty X] [Ring K] [Nontrivial K]
    [MulSemiringAction (Multiplicative ℤ) (LocallyConstant X K)] :
    Infinite (↥(elementaryGroup (Fin 3)
        (SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ))) ⧸
      Subgroup.center ↥(elementaryGroup (Fin 3)
        (SkewMonoidAlgebra (LocallyConstant X K) (Multiplicative ℤ)))) :=
  haveI : Nontrivial (LocallyConstant X K) := locallyConstant_nontrivial
  elementaryModCentre_skewMonoidAlgebra_infinite

/-! ### Model tests -/

/-- The trivial action of `ℤ` on a ring, used only to show that the instance hypotheses of
`elementaryModCentre_crossedProduct_infinite` can be met. -/
@[reducible] def trivialIntAction (R : Type*) [Semiring R] :
    MulSemiringAction (Multiplicative ℤ) R where
  smul _ r := r
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

/-- `EL₃(LC(Unit, 𝔽₂) ⋊ ℤ)/Z` is infinite (trivial action). -/
theorem trivialCrossedProduct_elementaryModCentre_infinite :
    letI := trivialIntAction (LocallyConstant Unit (ZMod 2))
    Infinite (↥(elementaryGroup (Fin 3)
        (SkewMonoidAlgebra (LocallyConstant Unit (ZMod 2)) (Multiplicative ℤ))) ⧸
      Subgroup.center ↥(elementaryGroup (Fin 3)
        (SkewMonoidAlgebra (LocallyConstant Unit (ZMod 2)) (Multiplicative ℤ)))) :=
  letI := trivialIntAction (LocallyConstant Unit (ZMod 2))
  haveI : Nontrivial (ZMod 2) := nontrivial_of_ne (0 : ZMod 2) 1 (by decide)
  elementaryModCentre_crossedProduct_infinite

end Pestov91
end GroupApproximation
