import Mathlib.Algebra.Module.Injective
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Every module over a field is injective

The dual Mayer–Vietoris short exact sequence needs the coefficient module to be
injective, so that `Hom(-, K)` is exact.  At `F₂` the vendored tree proves this as
`moduleInjective_ZMod2` (`H1ClassifierZMod2.lean` l.313) by Baer's criterion, with
a `fin_cases` that enumerates the two elements of `ZMod 2`.

Mathlib at the pin has no instance "every module over a field is injective" —
`Mathlib/Algebra/Module/Injective.lean` offers `Module.Baer.injective` and a `pi`
instance and nothing else — so the generic statement has to be proved here.

The proof does not go through Baer.  Over a field every submodule has a
complement (`Submodule.exists_isCompl`), so given an injective `f : X →ₗ[K] Y`
and any `g : X →ₗ[K] Q`, split `Y = range f ⊕ C` and extend `g` by `g ∘ f⁻¹` on
`range f` and `0` on `C`.  Mathlib packages exactly that composite as
`LinearMap.linearProjOfIsCompl`, whose defining lemma
`linearProjOfIsCompl_apply_left` is the whole content of the extension property.

Note that `Submodule.linearProjOfIsCompl_apply_left` is **deprecated** at this
pin, and a deprecation is a build error under the probe's `-DwarningAsError=true`;
the live name is in the `LinearMap` namespace and takes the complement first.

## Main declarations

* `moduleInjective_of_field` — `Module.Injective K Q` for any field `K` and any
  `K`-module `Q`.
-/

namespace GroupApproximation.CharClass

/-- **Every module over a field is injective.**  The generic replacement for the
vendored `moduleInjective_ZMod2`.

Over a field the range of an injective map is a direct summand, so the extension
is the composite of the projection onto that summand with the given map. -/
theorem moduleInjective_of_field (K Q : Type) [Field K] [AddCommGroup Q] [Module K Q] :
    Module.Injective K Q where
  out X Y _ _ _ _ f hf g := by
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range f)
    refine ⟨g ∘ₗ LinearMap.linearProjOfIsCompl C f hf hC, fun x => ?_⟩
    rw [LinearMap.comp_apply, LinearMap.linearProjOfIsCompl_apply_left]

/-- The `ZMod 2` instance of `moduleInjective_of_field`, for comparison with the
vendored `moduleInjective_ZMod2`. -/
theorem moduleInjective_zmod2 (Q : Type) [AddCommGroup Q] [Module (ZMod 2) Q] :
    Module.Injective (ZMod 2) Q :=
  moduleInjective_of_field (ZMod 2) Q

end GroupApproximation.CharClass
