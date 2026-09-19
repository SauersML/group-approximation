import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CohomologyCupProduct
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.RingTheory.Ideal.Lattice

/-!
# The Kronecker (evaluation) classifier `Hⁿ(X; F₂) → Hom(Hₙ(X; F₂), F₂)`

This file builds the **honest, general, build-clean** evaluation classifier map

```text
Hⁿ(X; F₂) ⟶ Hom_{F₂}(Hₙ(X; F₂), F₂)
```

for the project's constructed singular cohomology `cohomologyZMod2 X n`
(`= Hⁿ(Hom(C_•(X), F₂))`) and the singular homology `homologyZMod2 X n`
(`= Hₙ(C_•(X) ⊗ F₂)`) of the *same* `F₂` chain complex `C_•(X)` underlying the
project's cochain complex.

This is the canonical natural map of the universal-coefficient sequence: it
sends a cohomology class `[φ]` (the class of an `n`-cocycle `φ`) to the functional
`[z] ↦ φ(z)` (evaluate the cocycle on a homology cycle).  It is the classifier
map in the always-constructible direction.  Concretely it is built by descending,
through the cokernel presentation `Hₙ(C) = coker(∂ : C_{n+1} → Z_n(C))`, the
evaluation `Z_n(C) → F₂`, `c ↦ φ(c)`, which kills boundaries exactly because `φ`
is a cocycle (`δφ = ∂^* φ = 0`); the bundled map descends, through the
cokernel presentation of `Hⁿ(Hom(C, F₂))`, the linear assignment `cocycle ↦ its
Kronecker functional`, which kills coboundaries.

## Main declarations

* `chainCxZMod2 X` / `homologyZMod2 X n` — the `F₂` singular chain complex of `X`
  underlying the project's cochain complex, and its `n`-th homology object.
* `kroneckerFunctional X n φ hφ : Hₙ(X; F₂) ⟶ F₂` — the functional on homology
  defined by a cocycle `φ`.
* `kroneckerFunctional_homologyπ` — its defining factorization through `homologyπ`.
* `kroneckerFunctional_apply` — its value on a homology cycle class:
  `⟨[φ], [c]⟩ = φ(c)`.
* `kroneckerFunctional_add`, `kroneckerFunctional_smul` — `F₂`-linearity in the
  cocycle.
* `kroneckerFunctional_coboundary` — the functional of a coboundary is zero.
* `kroneckerMap X n : Hⁿ(X; F₂) ⟶ Hom_{F₂}(Hₙ(X; F₂), F₂)` — the bundled
  `F₂`-linear classifier map.
* `kroneckerMap_cocycleClass` — `kroneckerMap [φ] = kroneckerFunctional φ`.

## Scope / blocker

The map `kroneckerMap` is the universal-coefficient *evaluation* map.  Over the
field `F₂` it is an isomorphism (the universal coefficient theorem degenerates,
`Hom(−, F₂)` being exact); its **injectivity and surjectivity** require that
exactness, which is not available as a packaged instance in pinned Mathlib and is
the precise remaining input toward *inverting* the classifier (and thereby
producing a class `α ∈ H¹(RPⁿ; F₂)` from the monodromy character, together with a
degree-one Hurewicz comparison `π₁(X)ᵃᵇ ≅ H₁(X; ℤ)`).  No fake `α` and no fake
isomorphism are introduced here: only the genuine evaluation map is built.
-/

open CategoryTheory AlgebraicTopology Limits

noncomputable section

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The `F₂` singular chain complex of `X` underlying the project's cochain
complex `cochainCxZMod2 X = Hom(C_•(X), F₂)`. -/
abbrev chainCxZMod2 (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  ((singularChainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj
    (ModuleCat.of (ZMod 2) (ZMod 2))).obj X

/-- The `n`-th singular homology `Hₙ(X; F₂)`, as a `ModuleCat (ZMod 2)`-object. -/
abbrev homologyZMod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2) :=
  (chainCxZMod2 X).homology n

/-- The `F₂`-linear dual `Hom_{F₂}(Hₙ(X; F₂), F₂)` of singular homology, the
codomain of the Kronecker classifier. -/
abbrev homologyDualZMod2 (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} (ZMod 2) :=
  ModuleCat.of (ZMod 2) (homologyZMod2 X n →ₗ[ZMod 2] ZMod 2)

/-- Extensionality for maps out of `Hₙ(X; F₂)`: since `homologyπ` is an
epimorphism, two morphisms out of homology agree once they agree after
precomposition with `homologyπ`. -/
theorem homology_hom_ext {X : TopCat.{0}} {n : ℕ} {Z : ModuleCat.{0} (ZMod 2)}
    {f g : homologyZMod2 X n ⟶ Z}
    (h : (chainCxZMod2 X).homologyπ n ≫ f = (chainCxZMod2 X).homologyπ n ≫ g) :
    f = g :=
  (cancel_epi ((chainCxZMod2 X).homologyπ n)).1 h

/-- The cocycle condition rewritten on the chain differential: for a cocycle `φ`,
the composite `∂ ≫ (iCycles ≫ φ) = 0`, so `iCycles ≫ φ` descends along the
cokernel `homologyπ`. -/
theorem toCycles_iCycles_cochain_zero (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    (chainCxZMod2 X).toCycles (n + 1) n ≫ ((chainCxZMod2 X).iCycles n ≫ φ) = 0 := by
  rw [← Category.assoc, HomologicalComplex.toCycles_i]
  exact hφ

/-- The **Kronecker functional** of a cocycle `φ`: the `F₂`-linear functional on
`Hₙ(X; F₂)` obtained by descending the evaluation `Z_n(C) → F₂`, `c ↦ φ(c)`,
through the cokernel presentation `Hₙ(C) = coker(∂ : C_{n+1} → Z_n)`. -/
def kroneckerFunctional (X : TopCat.{0}) (n : ℕ) (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    homologyZMod2 X n ⟶ ModuleCat.of (ZMod 2) (ZMod 2) :=
  ((chainCxZMod2 X).homologyIsCokernel (n + 1) n (by simp [ComplexShape.prev])).desc
    (CokernelCofork.ofπ ((chainCxZMod2 X).iCycles n ≫ φ)
      (toCycles_iCycles_cochain_zero X n φ hφ))

/-- **Defining factorization** of the Kronecker functional: precomposing with
`homologyπ` recovers the evaluation `iCycles ≫ φ`. -/
theorem kroneckerFunctional_homologyπ (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    (chainCxZMod2 X).homologyπ n ≫ kroneckerFunctional X n φ hφ
      = (chainCxZMod2 X).iCycles n ≫ φ :=
  ((chainCxZMod2 X).homologyIsCokernel (n + 1) n (by simp [ComplexShape.prev])).fac
    (CokernelCofork.ofπ ((chainCxZMod2 X).iCycles n ≫ φ)
      (toCycles_iCycles_cochain_zero X n φ hφ)) WalkingParallelPair.one

/-- **Value of the Kronecker functional on a homology cycle class.**  For a
cycle `c ∈ Z_n(C)`, the Kronecker functional of a cocycle `φ` sends the homology
class `homologyπ c` to `φ(c)`. -/
theorem kroneckerFunctional_apply (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (c : (chainCxZMod2 X).cycles n) :
    (kroneckerFunctional X n φ hφ).hom (((chainCxZMod2 X).homologyπ n).hom c)
      = φ.hom (((chainCxZMod2 X).iCycles n).hom c) := by
  have h := kroneckerFunctional_homologyπ X n φ hφ
  have h2 := congrArg
    (fun (m : (chainCxZMod2 X).cycles n ⟶ ModuleCat.of (ZMod 2) (ZMod 2)) => m.hom c) h
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/--
The Kronecker functional is additive in the cocycle.
-/
theorem kroneckerFunctional_add (X : TopCat.{0}) (n : ℕ)
    (φ ψ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0) (hψ : cochainCoboundary (ZMod 2) X n ψ = 0)
    (hφψ : cochainCoboundary (ZMod 2) X n (φ + ψ) = 0) :
    kroneckerFunctional X n (φ + ψ) hφψ
      = kroneckerFunctional X n φ hφ + kroneckerFunctional X n ψ hψ := by
  apply homology_hom_ext;
  simp_all +decide [ kroneckerFunctional_homologyπ, Preadditive.comp_add ]

/--
The Kronecker functional is `F₂`-homogeneous in the cocycle.
-/
theorem kroneckerFunctional_smul (X : TopCat.{0}) (n : ℕ) (s : ZMod 2)
    (φ : singularCochainGroup (ZMod 2) X n)
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (hsφ : cochainCoboundary (ZMod 2) X n (s • φ) = 0) :
    kroneckerFunctional X n (s • φ) hsφ = s • kroneckerFunctional X n φ hφ := by
  apply homology_hom_ext;
  simp +decide [ kroneckerFunctional_homologyπ ]

/--
The Kronecker functional of the zero cocycle is zero.
-/
theorem kroneckerFunctional_zero (X : TopCat.{0}) (n : ℕ)
    (h0 : cochainCoboundary (ZMod 2) X n (0 : singularCochainGroup (ZMod 2) X n) = 0) :
    kroneckerFunctional X n 0 h0 = 0 := by
  apply homology_hom_ext;
  rw [ kroneckerFunctional_homologyπ ];
  simp +zetaDelta at *

/--
**The Kronecker functional of a coboundary is zero.**  A coboundary `φ = δη`
evaluated on a homology cycle class vanishes, because `δη(z) = η(∂z) = η(0) = 0`
for a cycle `z`.
-/
theorem kroneckerFunctional_coboundary (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup (ZMod 2) X m)
    (hcoc : cochainCoboundary (ZMod 2) X (m + 1) (cochainCoboundary (ZMod 2) X m η) = 0) :
    kroneckerFunctional X (m + 1) (cochainCoboundary (ZMod 2) X m η) hcoc = 0 := by
  apply homology_hom_ext;
  rw [ kroneckerFunctional_homologyπ ];
  rw [ show cochainCoboundary ( ZMod 2 ) X m η = ( chainCxZMod2 X ).d ( m + 1 ) m ≫ η from rfl ] ; aesop;

/-- Proof-irrelevance of the cocycle hypothesis: the Kronecker functional only
depends on the cochain. -/
theorem kroneckerFunctional_congr (X : TopCat.{0}) (n : ℕ)
    {φ φ' : singularCochainGroup (ZMod 2) X n} (h : φ = φ')
    (hφ : cochainCoboundary (ZMod 2) X n φ = 0)
    (hφ' : cochainCoboundary (ZMod 2) X n φ' = 0) :
    kroneckerFunctional X n φ hφ = kroneckerFunctional X n φ' hφ' := by
  subst h; rfl

/--
Additivity content of the Kronecker cycles-map (the `map_add'` field).
-/
theorem kroneckerFunctional_iCycles_add (X : TopCat.{0}) (n : ℕ)
    (c c' : (cochainCxZMod2 X).cycles n) :
    (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom (c + c'))
        (cochainCoboundary_iCycles X n (c + c'))).hom
      = (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c)
          (cochainCoboundary_iCycles X n c)).hom
        + (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c')
            (cochainCoboundary_iCycles X n c')).hom := by
  have hsum : cochainCoboundary (ZMod 2) X n
      (((cochainCxZMod2 X).iCycles n).hom c +
        ((cochainCxZMod2 X).iCycles n).hom c') = 0 := by
    simpa only [map_add] using cochainCoboundary_iCycles X n (c + c')
  convert congrArg ModuleCat.Hom.hom
    (kroneckerFunctional_add X n _ _
      (cochainCoboundary_iCycles X n c)
      (cochainCoboundary_iCycles X n c')
      hsum) using 1 <;> simp

/--
Homogeneity content of the Kronecker cycles-map (the `map_smul'` field).
-/
theorem kroneckerFunctional_iCycles_smul (X : TopCat.{0}) (n : ℕ) (s : ZMod 2)
    (c : (cochainCxZMod2 X).cycles n) :
    (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom (s • c))
        (cochainCoboundary_iCycles X n (s • c))).hom
      = s • (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c)
          (cochainCoboundary_iCycles X n c)).hom := by
  have hsmul : cochainCoboundary (ZMod 2) X n
      (s • ((cochainCxZMod2 X).iCycles n).hom c) = 0 := by
    simpa only [map_smul] using cochainCoboundary_iCycles X n (s • c)
  convert congrArg ModuleCat.Hom.hom
    (kroneckerFunctional_smul X n s _
      (cochainCoboundary_iCycles X n c)
      hsmul) using 1 <;> simp

/-- The Kronecker functional, packaged as an `F₂`-linear map from the
cohomology cocycles (the `cycles` of the cochain complex) to the homology dual,
sending a cochain `cycle` `c` to the Kronecker functional of the cocycle
`iCycles c`. -/
def kroneckerCyclesMap (X : TopCat.{0}) (n : ℕ) :
    (cochainCxZMod2 X).cycles n ⟶ homologyDualZMod2 X n :=
  ModuleCat.ofHom
    { toFun := fun c =>
        (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c)
          (cochainCoboundary_iCycles X n c)).hom
      map_add' := kroneckerFunctional_iCycles_add X n
      map_smul' := kroneckerFunctional_iCycles_smul X n }

@[simp] theorem kroneckerCyclesMap_hom_apply (X : TopCat.{0}) (n : ℕ)
    (c : (cochainCxZMod2 X).cycles n) :
    (kroneckerCyclesMap X n).hom c
      = (kroneckerFunctional X n (((cochainCxZMod2 X).iCycles n).hom c)
          (cochainCoboundary_iCycles X n c)).hom := rfl

/--
The Kronecker cycles-map kills coboundaries, hence descends along the
cohomology cokernel `homologyπ`.
-/
theorem kroneckerCyclesMap_toCycles (X : TopCat.{0}) (n : ℕ) :
    (cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ kroneckerCyclesMap X n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change (kroneckerFunctional X n
    (((cochainCxZMod2 X).iCycles n).hom
      (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w)) _).hom = 0
  apply congrArg ModuleCat.Hom.hom
  apply homology_hom_ext
  rw [kroneckerFunctional_homologyπ]
  have hcochain :
      ((cochainCxZMod2 X).iCycles n).hom
          (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w) =
        ((cochainCxZMod2 X).d ((ComplexShape.up ℕ).prev n) n).hom w :=
    ConcreteCategory.congr_hom
      ((cochainCxZMod2 X).toCycles_i ((ComplexShape.up ℕ).prev n) n) w
  change (chainCxZMod2 X).iCycles n ≫
      (((cochainCxZMod2 X).iCycles n).hom
        (((cochainCxZMod2 X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w)) = 0
  rw [hcochain]
  change (chainCxZMod2 X).iCycles n ≫
      ((chainCxZMod2 X).d n ((ComplexShape.up ℕ).prev n) ≫ w) = 0
  rw [← Category.assoc, (chainCxZMod2 X).iCycles_d, zero_comp]

/-- **The Kronecker (evaluation) classifier map**
`Hⁿ(X; F₂) ⟶ Hom_{F₂}(Hₙ(X; F₂), F₂)`, the canonical natural map of the
universal-coefficient sequence, sending `[φ] ↦ ([z] ↦ φ(z))`. -/
def kroneckerMap (X : TopCat.{0}) (n : ℕ) :
    cohomologyZMod2 X n ⟶ homologyDualZMod2 X n :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).desc
    (CokernelCofork.ofπ (kroneckerCyclesMap X n) (kroneckerCyclesMap_toCycles X n))

/-- The defining factorization of `kroneckerMap` through the cohomology cokernel
projection `homologyπ`. -/
theorem kroneckerMap_homologyπ (X : TopCat.{0}) (n : ℕ) :
    (cochainCxZMod2 X).homologyπ n ≫ kroneckerMap X n = kroneckerCyclesMap X n :=
  ((cochainCxZMod2 X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).fac
    (CokernelCofork.ofπ (kroneckerCyclesMap X n) (kroneckerCyclesMap_toCycles X n))
    WalkingParallelPair.one

/--
The Kronecker classifier on the class of a cocycle `φ` is the Kronecker
functional of `φ`: `kroneckerMap [φ] = ([z] ↦ φ(z))`.
-/
theorem kroneckerMap_cocycleClass (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup (ZMod 2) X n) (hφ : cochainCoboundary (ZMod 2) X n φ = 0) :
    (kroneckerMap X n).hom (cocycleClass X n φ hφ)
      = (kroneckerFunctional X n φ hφ).hom := by
  unfold cocycleClass
  rw [← ModuleCat.comp_apply, kroneckerMap_homologyπ,
    kroneckerCyclesMap_hom_apply]
  exact congrArg ModuleCat.Hom.hom
    (kroneckerFunctional_congr X n (iCycles_cyclesMk X n φ hφ) _ _)

/-- The cycle-inclusion `iCycles : Z_n(C) ↪ C_n` is injective (it is a mono), so
its kernel is trivial. -/
theorem chainCxZMod2_iCycles_ker (X : TopCat.{0}) (n : ℕ) :
    LinearMap.ker ((chainCxZMod2 X).iCycles n).hom = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  exact (ModuleCat.mono_iff_injective ((chainCxZMod2 X).iCycles n)).1 inferInstance

/-- **Every `F₂`-module is injective** (`ZMod 2` is a field, so Baer's criterion
holds: a map from an ideal `⊥`/`⊤` of the field extends to the whole ring). -/
theorem moduleInjective_ZMod2 (M : Type) [AddCommGroup M] [Module (ZMod 2) M] :
    Module.Injective (ZMod 2) M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Module.Baer.injective
  intro I g
  rcases eq_or_ne I ⊥ with h | h
  · subst h
    refine ⟨0, fun x mem => ?_⟩
    have hx : (⟨x, mem⟩ : ↑(⊥ : Ideal (ZMod 2))) = 0 := by
      apply Subtype.ext; simpa using mem
    rw [hx, map_zero]; rfl
  · have htop : I = ⊤ := by
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
      rw [Ideal.eq_top_iff_one]
      have ha1 : a = 1 := by
        fin_cases a
        · exact (ha0 rfl).elim
        · rfl
      rwa [ha1] at ha
    subst htop
    refine ⟨{ toFun := fun x => g ⟨x, Submodule.mem_top⟩, map_add' := ?_, map_smul' := ?_ }, ?_⟩
    · intro a b; rw [← map_add]; rfl
    · intro c a; rw [← map_smul]; rfl
    · intro x mem; rfl

/-- **The cycle inclusion splits over the field `F₂`.**  The mono
`iCycles : Z_n(C) ↪ C_n` admits a `ModuleCat`-retraction `s` with
`iCycles ≫ s = 𝟙`.  This holds because over a field every module is injective
(Baer's criterion), so the short exact sequence of the inclusion splits. -/
theorem chainCxZMod2_iCycles_split (X : TopCat.{0}) (n : ℕ) :
    ∃ s : (chainCxZMod2 X).X n ⟶ (chainCxZMod2 X).cycles n,
      (chainCxZMod2 X).iCycles n ≫ s = 𝟙 ((chainCxZMod2 X).cycles n) := by
  haveI : Module.Injective (ZMod 2) ((chainCxZMod2 X).cycles n) :=
    moduleInjective_ZMod2 _
  haveI : CategoryTheory.Injective ((chainCxZMod2 X).cycles n) :=
    Module.injective_object_of_injective_module (ZMod 2) ((chainCxZMod2 X).cycles n)
  exact ⟨CategoryTheory.Injective.factorThru (𝟙 _) ((chainCxZMod2 X).iCycles n),
    CategoryTheory.Injective.comp_factorThru _ _⟩

/-- **Surjectivity of the Kronecker classifier (universal coefficient theorem,
`F₂` direction).**  Over the field `F₂` every linear functional on `Hₙ(X; F₂)`
is the Kronecker functional `[z] ↦ φ(z)` of some cocycle `φ`; equivalently, the
classifier map `kroneckerMap X n` is surjective.

This is the *constructive* universal-coefficient direction: a class
`a ∈ Hⁿ(X; F₂)` can be produced from any functional on homology.  Its proof uses
that the inclusion of cycles `iCycles : Z_n(C) ↪ C_n` is split injective over a
field (`LinearMap.exists_leftInverse_of_injective`): a left inverse `r` lets us
extend the functional `g ∘ homologyπ : Z_n → F₂` to a cochain `φ := g ∘ homologyπ
∘ r : C_n → F₂`, which is automatically a cocycle (it vanishes on boundaries,
since `homologyπ` does) and whose class maps to `g`. -/
theorem kroneckerMap_surjective (X : TopCat.{0}) (n : ℕ) :
    Function.Surjective (kroneckerMap X n).hom := by
  intro g
  obtain ⟨s, hs⟩ := chainCxZMod2_iCycles_split X n
  have hs_app : ∀ x, s.hom (((chainCxZMod2 X).iCycles n).hom x) = x := by
    intro x
    have := congrArg (fun (m : (chainCxZMod2 X).cycles n ⟶ (chainCxZMod2 X).cycles n) => m.hom x) hs
    simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  set φ : singularCochainGroup (ZMod 2) X n :=
    ModuleCat.ofHom ((g ∘ₗ ((chainCxZMod2 X).homologyπ n).hom) ∘ₗ s.hom) with hφdef
  have h_r_iCycles : (chainCxZMod2 X).iCycles n ≫ φ
      = (chainCxZMod2 X).homologyπ n ≫ ModuleCat.ofHom g := by
    ext c
    simp only [φ, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, hs_app]
  have h_phi_cocycle : cochainCoboundary (ZMod 2) X n φ = 0 := by
    have h1 : (chainCxZMod2 X).d (n + 1) n ≫ φ
        = (chainCxZMod2 X).toCycles (n + 1) n ≫ (chainCxZMod2 X).homologyπ n ≫ ModuleCat.ofHom g := by
      rw [← h_r_iCycles, ← Category.assoc, HomologicalComplex.toCycles_i]
    show (chainCxZMod2 X).d (n + 1) n ≫ φ = 0
    rw [h1, ← Category.assoc, HomologicalComplex.toCycles_comp_homologyπ, zero_comp]
  refine ⟨cocycleClass X n φ h_phi_cocycle, ?_⟩
  rw [kroneckerMap_cocycleClass]
  have hkf : kroneckerFunctional X n φ h_phi_cocycle = ModuleCat.ofHom g := by
    apply homology_hom_ext
    rw [kroneckerFunctional_homologyπ, h_r_iCycles]
  rw [hkf, ModuleCat.hom_ofHom]

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
