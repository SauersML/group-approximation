import GroupApproximation.CharClass.MayerVietorisElement
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionHomotopyFormula

/-!
# The Mayer–Vietoris restrictions are restrictions: the chain-level half

`MayerVietorisElement.lean` defines `mvResU`, `mvResV`, `mvResWU`, `mvResWV` through the
dualized Mayer–Vietoris sequence, so `mvResWU_apply` unfolds them to a composite of a
homology map with two identification isomorphisms.  Consumers (cc-projective's
projective-space induction, and Leray–Hirsch after it) need them identified with the
honest pullback `pull (inclSubtype _)` along the inclusion of subspaces — in the first
instance only in degree zero, where it says the unit restricts to the unit.

The mathematical content of that identification is a single naturality square at the
level of *chains*, and it is what this file proves:

```text
        C_*(↥S) --singularChainMap (ι : ↥S ⟶ ↥T)--> C_*(↥T)
           |                                           |
   subChainCorestrict S                        subChainCorestrict T
           v                                           v
     C_*^S(X)  ------subChainInclusion S T------>  C_*^T(X)
```

Both composites send a chain of the subspace to the same chain of `X`, because
`ι ≫ sInclusion T = sInclusion S`; everything else is functoriality of
`singularChainMap`.  Dualizing this square and conjugating by `subCxDualHomologyIso` is
what turns `mvResWU` into `cohPullback (subInclusion _)`; that remaining step is
recorded in `notes/lix-lane-reports/cc-thom.md`.

## Main results

* `subInclusion` — the inclusion `↥S ⟶ ↥T` of subspaces, and
  `subInclusion_comp_sInclusion`.
* `subChainCorestrict_naturality` — the square above.
-/

namespace GroupApproximation.CharClass

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

variable {X : TopCat.{0}}

/-- The singular chain complex functor with `F₂` coefficients.  `singularChainMap R f n`
is its degree-`n` component; the naturality square below is an equality of chain
*complex* maps, so it is this functor that appears rather than `singularChainMap`. -/
abbrev chainCxFun : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))

/-- The inclusion `↥S ⟶ ↥T` of subspaces of `X`, for `S ⊆ T`. -/
def subInclusion {S T : Set X} (h : S ⊆ T) : TopCat.of S ⟶ TopCat.of T :=
  TopCat.ofHom ⟨fun x => ⟨(x : X), h x.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion of subspaces followed by the inclusion of the bigger subspace into the
ambient space is the inclusion of the smaller one. -/
theorem subInclusion_comp_sInclusion {S T : Set X} (h : S ⊆ T) :
    subInclusion h ≫ sInclusion T = sInclusion S := rfl

/-- **`subChainCorestrict` is natural for inclusions of subspaces.**  This is the whole
mathematical content of "the Mayer–Vietoris restrictions are the honest restrictions":
both composites push a chain of `↥S` into the chains of `X` along the same map. -/
theorem subChainCorestrict_naturality {S T : Set X} (h : S ⊆ T) :
    subChainCorestrict (ZMod 2) X S ≫ subChainInclusion S T h
      = chainCxFun.map (subInclusion h) ≫ subChainCorestrict (ZMod 2) X T := by
  have hc : chainCxFun.map (subInclusion h) ≫ chainCxFun.map (sInclusion T)
      = chainCxFun.map (sInclusion S) := by
    rw [← CategoryTheory.Functor.map_comp, subInclusion_comp_sInclusion]
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  have hn : (chainCxFun.map (subInclusion h)).f n ≫ (chainCxFun.map (sInclusion T)).f n
      = (chainCxFun.map (sInclusion S)).f n := by
    rw [← HomologicalComplex.comp_f, hc]
  exact (hom_apply_of_comp_eq hn c).symm

end

end GroupApproximation.CharClass
