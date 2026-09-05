import GroupApproximation.KTheory.Functorial
import Mathlib.Analysis.CStarAlgebra.ContinuousMap

/-!
# `K⁰` of a space, and its contravariance

`lix-design`'s §B.4 fixes the campaign's convention: `K⁰(X) := K₀(C(X))`, with
no Serre--Swan and no bundle theory.  `KTheory/Basic.lean` builds `K₀` of a
`*`-ring and `KTheory/Functorial.lean` makes it a functor of that ring, so this
file is only the specialization, and it is three definitions long.

The coefficient ring is `C(X, ℂ)`, which carries the `NonUnitalSemiring` and
`StarRing` that `KZero` asks for as soon as `X` is a topological space --
compactness is *not* needed to form the group.  It is needed for `K₀(C(X))` to
be `K⁰(X)` in the sense of vector bundles, since that is where Serre--Swan
lives; nothing below depends on it, so nothing below assumes it.

Contravariance is the composite of two functorialities already proved: `KZero`
in its coefficient ring, and `X ↦ C(X, ℂ)` in the space.  The second is
`ContinuousMap.compStarAlgHom'`, a `StarAlgHom`, and it feeds `KZero.map`
directly because every `StarAlgHom` is a `NonUnitalStarRingHomClass`; no
conversion lemma is needed.
-/

namespace GroupApproximation
namespace KTheory

/-- **`K⁰(X)`**, in the campaign's convention `K⁰(X) = K₀(C(X))`.

For compact Hausdorff `X` this is the Grothendieck group of stable isomorphism
classes of complex vector bundles on `X`, presented by projections in matrix
algebras over `C(X, ℂ)`. -/
abbrev KZeroSpace (X : Type*) [TopologicalSpace X] :=
  KZero C(X, ℂ)

/-- Pullback of continuous functions, as a coefficient `*`-homomorphism.

This is `ContinuousMap.compStarAlgHom'` with `map_one'` and `commutes'`
forgotten, written out rather than coerced: the coercion from a `StarAlgHom`
runs through `NonUnitalAlgHomClass F R A B`, whose scalar ring `R` is a
non-out-param and would have to be guessed by instance search.  Every field
below is `rfl` except the zero, exactly as in the Mathlib definition. -/
def pullbackCoeffHom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : C(Y, ℂ) →⋆ₙ+* C(X, ℂ) where
  toFun g := g.comp f
  map_mul' _ _ := rfl
  map_zero' := ContinuousMap.zero_comp f
  map_add' _ _ := rfl
  map_star' _ := rfl

/-- **`K⁰` is contravariant in the space.** -/
noncomputable def KZeroSpace.map {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : KZeroSpace Y →+ KZeroSpace X :=
  KZero.map (pullbackCoeffHom f)

end KTheory
end GroupApproximation
