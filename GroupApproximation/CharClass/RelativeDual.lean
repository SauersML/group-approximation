import GroupApproximation.CharClass.RelativeCochains

/-!
# Dualization of chain complexes over a field, and quasi-isomorphisms

The singular cochain complex of the vendored development is the `Hom(-, R)`-dual of
the singular chain complex.  Over `ZMod 2` — indeed over any ring for which the
coefficient module is injective — the dualizing functor is exact, so it takes a
quasi-isomorphism of chain complexes to a quasi-isomorphism of cochain complexes.

That is the one homological input excision needs beyond the vendored small-chains
theorem: the small-chain inclusion is a quasi-isomorphism of chain complexes
(`smallChains_inclusion_quasiIso`), and this file upgrades it to the statement that
restricting cochains to small chains is a quasi-isomorphism of cochain complexes.

## Main definitions

* `dualFunctor R` — the dualizing functor `Hom(-, R) : (ModuleCat R)ᵒᵖ ⥤ ModuleCat R`.
* `dualCx R K`, `dualMap R f` — the dual cochain complex of a chain complex and the
  dual of a chain map.

## Main results

* `dualFunctor_preservesLimits`, `dualFunctorZMod2_preservesEpimorphisms`,
  `dualFunctorZMod2_preservesHomology` — exactness of `Hom(-, ZMod 2)`.
* the instance `QuasiIso (dualMap (ZMod 2) f)` for a quasi-isomorphism `f`.
* `cochainCx_eq_dualCx` — the singular cochain complex is the dual of the singular
  chain complex (by `rfl`).
-/

open CategoryTheory Limits AlgebraicTopology
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-! ## 1. The dualizing functor is exact over `ZMod 2` -/

/-- The dualizing functor `Hom(-, R) : (ModuleCat R)ᵒᵖ ⥤ ModuleCat R`; this is the
functor used by the vendored `singularCochainComplexFunctor`. -/
abbrev dualFunctor (R : Type) [CommRing R] :
    (ModuleCat.{0} R)ᵒᵖ ⥤ ModuleCat.{0} R :=
  (linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)

instance dualFunctor_preservesLimits (R : Type) [CommRing R] :
    PreservesLimits (dualFunctor R) :=
  have : PreservesLimits (dualFunctor R ⋙ forget (ModuleCat.{0} R)) :=
    (inferInstance : PreservesLimits (yoneda.obj (ModuleCat.of R R)))
  preservesLimits_of_reflects_of_preserves _ (forget _)

/-- `Hom(-, ZMod 2)` turns monomorphisms into epimorphisms: `ZMod 2` is an injective
module over itself (it is a field). -/
instance dualFunctorZMod2_preservesEpimorphisms :
    (dualFunctor (ZMod 2)).PreservesEpimorphisms where
  preserves {A B} f hf := by
    haveI := hf
    haveI : Mono f.unop := inferInstance
    haveI : Module.Injective (ZMod 2) (ZMod 2) := moduleInjective_ZMod2 (ZMod 2)
    rw [ModuleCat.epi_iff_surjective]
    intro ψ
    obtain ⟨h, hh⟩ := Module.Injective.out (R := ZMod 2) (Q := ZMod 2)
      (f.unop).hom ((ModuleCat.mono_iff_injective f.unop).1 inferInstance) ψ.hom
    refine ⟨ModuleCat.ofHom h, ?_⟩
    show f.unop ≫ ModuleCat.ofHom h = ψ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hh x

instance dualFunctorZMod2_preservesHomology :
    (dualFunctor (ZMod 2)).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-! ## 2. The dual complex -/

/-- The dual cochain complex of a chain complex. -/
abbrev dualCx (R : Type) [CommRing R] (K : ChainComplex (ModuleCat.{0} R) ℕ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  ((dualFunctor R).mapHomologicalComplex _).obj
    ((HomologicalComplex.opFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).obj
      (Opposite.op K))

/-- The dual of a chain map. -/
abbrev dualMap (R : Type) [CommRing R] {K L : ChainComplex (ModuleCat.{0} R) ℕ}
    (f : K ⟶ L) : dualCx R L ⟶ dualCx R K :=
  ((dualFunctor R).mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map f.op)

/-- **The dual of a quasi-isomorphism is a quasi-isomorphism** over `ZMod 2`. -/
instance dualMap_quasiIso {K L : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} (f : K ⟶ L)
    [QuasiIso f] : QuasiIso (dualMap (ZMod 2) f) :=
  inferInstanceAs (QuasiIso (((dualFunctor (ZMod 2)).mapHomologicalComplex _).map
    ((HomologicalComplex.opFunctor (ModuleCat.{0} (ZMod 2))
      (ComplexShape.down ℕ)).map f.op)))

/-- The singular cochain complex is the dual of the singular chain complex. -/
theorem cochainCx_eq_dualCx (R : Type) [CommRing R] (X : TopCat.{0}) :
    cochainCx R X = dualCx R (singularChainComplex R X) := rfl

end

end GroupApproximation.CharClass
