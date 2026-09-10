import GroupApproximation.CharClass.CoeffCohomology
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.H1ClassifierZMod2

/-!
# The Kronecker (evaluation) classifier over an arbitrary coefficient ring

`ThirdParty/.../H1ClassifierZMod2.lean` builds the evaluation classifier

```text
kroneckerMap X n : Hⁿ(X; F₂) ⟶ Hom_{F₂}(Hₙ(X; F₂), F₂)
```

and `KroneckerNaturality.lean` upgrades it to an isomorphism.  Both are pinned at
`ZMod 2`, and `kroneckerEquiv X n` takes no coefficient parameter at all, which is why
`sp-coeff`'s census records the whole universal-coefficient layer as the one part of the
`CharClass` stack that is genuinely `ZMod 2`-only.  This lane ports it.

**Nothing vendored is edited.**  The `ZMod 2` names stay exactly where they are and keep
their proofs; this file adds generic twins with the `…Of` suffix, and §4 records that each
twin *is* the vendored object at `K = ZMod 2`, by `rfl`.  That is the pattern
`CoeffLeibniz.lean` established, and it keeps the `F₂` instance — the verified LIX
answer — incapable of moving.

## This file

The first step of the port: the chain complex, its homology and dual, and the Kronecker
functional of a cocycle with its two linearity lemmas.  `[CommRing K]` throughout; the
field is not needed until the cycle inclusion has to split, which is the next file.

The two linearity lemmas are the reason this step is probed on its own.  The vendored
proofs close them with `simp_all +decide` and `simp +decide`, and `decide` cannot run over
an abstract `K`.  Both are proved here from the defining factorisation instead, with no
`decide` and no characteristic hypothesis: additivity is `Preadditive.comp_add` and
homogeneity is `Linear.comp_smul`, on either side of `kroneckerFunctionalOf_homologyπ`.
-/

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace GroupApproximation
namespace CharClass

/-! ## 1. The chain complex, its homology, and the dual -/

/-- The singular chain complex of `X` with coefficients in `K`, the object underlying the
cochain complex `cochainCxK K X = Hom(C_•(X), K)`. -/
abbrev chainCxOf (K : Type) [CommRing K] (X : TopCat.{0}) :
    ChainComplex (ModuleCat.{0} K) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} K)).obj (ModuleCat.of K K)).obj X

/-- The `n`-th singular homology `Hₙ(X; K)`. -/
abbrev homologyOf (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} K :=
  (chainCxOf K X).homology n

/-- The `K`-linear dual `Hom_K(Hₙ(X; K), K)`, the codomain of the classifier. -/
abbrev homologyDualOf (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} K :=
  ModuleCat.of K (homologyOf K X n →ₗ[K] K)

/-- Extensionality for maps out of `Hₙ(X; K)`: `homologyπ` is an epimorphism. -/
theorem homology_hom_extOf {K : Type} [CommRing K] {X : TopCat.{0}} {n : ℕ}
    {Z : ModuleCat.{0} K} {f g : homologyOf K X n ⟶ Z}
    (h : (chainCxOf K X).homologyπ n ≫ f = (chainCxOf K X).homologyπ n ≫ g) :
    f = g :=
  (cancel_epi ((chainCxOf K X).homologyπ n)).1 h

/-! ## 2. The Kronecker functional of a cocycle -/

/-- The cocycle condition on the chain differential: for a cocycle `φ` the composite
`∂ ≫ (iCycles ≫ φ)` vanishes, so `iCycles ≫ φ` descends along the cokernel `homologyπ`. -/
theorem toCycles_iCycles_cochain_zeroOf (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0) :
    (chainCxOf K X).toCycles (n + 1) n ≫ ((chainCxOf K X).iCycles n ≫ φ) = 0 := by
  rw [← Category.assoc, HomologicalComplex.toCycles_i]
  exact hφ

/-- **The Kronecker functional** of a cocycle `φ`: the `K`-linear functional on `Hₙ(X; K)`
obtained by descending the evaluation `Z_n(C) → K`, `c ↦ φ(c)`, through the cokernel
presentation `Hₙ(C) = coker(∂ : C_{n+1} → Z_n)`. -/
def kroneckerFunctionalOf (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0) :
    homologyOf K X n ⟶ ModuleCat.of K K :=
  ((chainCxOf K X).homologyIsCokernel (n + 1) n (by simp [ComplexShape.prev])).desc
    (CokernelCofork.ofπ ((chainCxOf K X).iCycles n ≫ φ)
      (toCycles_iCycles_cochain_zeroOf K X n φ hφ))

/-- **Defining factorisation**: precomposing with `homologyπ` recovers `iCycles ≫ φ`. -/
theorem kroneckerFunctionalOf_homologyπ (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0) :
    (chainCxOf K X).homologyπ n ≫ kroneckerFunctionalOf K X n φ hφ
      = (chainCxOf K X).iCycles n ≫ φ :=
  ((chainCxOf K X).homologyIsCokernel (n + 1) n (by simp [ComplexShape.prev])).fac
    (CokernelCofork.ofπ ((chainCxOf K X).iCycles n ≫ φ)
      (toCycles_iCycles_cochain_zeroOf K X n φ hφ)) WalkingParallelPair.one

/-- **Value on a cycle class**: the functional sends `homologyπ c` to `φ(c)`. -/
theorem kroneckerFunctionalOf_apply (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0)
    (c : (chainCxOf K X).cycles n) :
    (kroneckerFunctionalOf K X n φ hφ).hom (((chainCxOf K X).homologyπ n).hom c)
      = φ.hom (((chainCxOf K X).iCycles n).hom c) := by
  have h := kroneckerFunctionalOf_homologyπ K X n φ hφ
  have h2 := congrArg
    (fun (m : (chainCxOf K X).cycles n ⟶ ModuleCat.of K K) => m.hom c) h
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-! ## 3. Linearity in the cocycle

The vendored proofs of these two use `decide`, which has no meaning over an abstract `K`.
Both follow from the defining factorisation and one additivity or homogeneity law of the
ambient linear category, with no characteristic hypothesis. -/

/-- **The Kronecker functional is additive in the cocycle.** -/
theorem kroneckerFunctionalOf_add (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup K X n)
    (hφ : cochainCoboundary K X n φ = 0) (hψ : cochainCoboundary K X n ψ = 0)
    (hφψ : cochainCoboundary K X n (φ + ψ) = 0) :
    kroneckerFunctionalOf K X n (φ + ψ) hφψ
      = kroneckerFunctionalOf K X n φ hφ + kroneckerFunctionalOf K X n ψ hψ := by
  apply homology_hom_extOf
  -- split the composite on the RIGHT first: `homologyπ ≫ (kF φ + kF ψ)` is not of the
  -- form the defining factorisation matches until the sum is distributed.
  rw [Preadditive.comp_add, kroneckerFunctionalOf_homologyπ, kroneckerFunctionalOf_homologyπ,
    kroneckerFunctionalOf_homologyπ, Preadditive.comp_add]

/-- **The Kronecker functional is `K`-homogeneous in the cocycle.** -/
theorem kroneckerFunctionalOf_smul (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) (s : K)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0)
    (hsφ : cochainCoboundary K X n (s • φ) = 0) :
    kroneckerFunctionalOf K X n (s • φ) hsφ = s • kroneckerFunctionalOf K X n φ hφ := by
  apply homology_hom_extOf
  rw [Linear.comp_smul, kroneckerFunctionalOf_homologyπ, kroneckerFunctionalOf_homologyπ,
    Linear.comp_smul]

/-- **The functional of the zero cocycle is zero.** -/
theorem kroneckerFunctionalOf_zero (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (h0 : cochainCoboundary K X n (0 : singularCochainGroup K X n) = 0) :
    kroneckerFunctionalOf K X n 0 h0 = 0 := by
  apply homology_hom_extOf
  rw [kroneckerFunctionalOf_homologyπ, Limits.comp_zero, Limits.comp_zero]

/-- The functional depends only on the cochain, not on the cocycle proof. -/
theorem kroneckerFunctionalOf_congr (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup K X n} (h : φ = φ')
    (hφ : cochainCoboundary K X n φ = 0) (hφ' : cochainCoboundary K X n φ' = 0) :
    kroneckerFunctionalOf K X n φ hφ = kroneckerFunctionalOf K X n φ' hφ' := by
  subst h
  rfl

/-! ## 4. The `ZMod 2` instance is the vendored object

Each generic name is *definitionally* the vendored `ZMod 2` one, so the `F₂` layer is not
a copy of this development but literally its instance. -/

theorem chainCxOf_zmod2 (X : TopCat.{0}) : chainCxOf (ZMod 2) X = chainCxZMod2 X := rfl

theorem homologyOf_zmod2 (X : TopCat.{0}) (n : ℕ) :
    homologyOf (ZMod 2) X n = homologyZMod2 X n := rfl

theorem homologyDualOf_zmod2 (X : TopCat.{0}) (n : ℕ) :
    homologyDualOf (ZMod 2) X n = homologyDualZMod2 X n := rfl

theorem kroneckerFunctionalOf_zmod2 (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    kroneckerFunctionalOf (ZMod 2) X n φ hφ = kroneckerFunctional X n φ hφ := rfl

end CharClass
end GroupApproximation

end
