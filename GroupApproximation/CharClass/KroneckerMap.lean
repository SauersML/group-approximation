import GroupApproximation.CharClass.KroneckerClassifier
import GroupApproximation.CharClass.CoeffField

/-!
# The Kronecker classifier map, and its surjectivity over a field

Step 2 of the universal-coefficient port: `kroneckerFunctionalOf` of
`KroneckerClassifier.lean` is packaged into the classifier

```text
kroneckerMapOf K X n : Hⁿ(X; K) ⟶ Hom_K(Hₙ(X; K), K)
```

and shown surjective.  This is the constructive direction of the universal coefficient
theorem: a class in `Hⁿ(X; K)` can be produced from any functional on homology.

## Where the field is needed, and where it is not

`[CommRing K]` carries everything down to `kroneckerMapOf` and its computation rule on the
class of a cocycle.  `[Field K]` enters at exactly one place, `chainCxOf_iCycles_split`:
the inclusion of cycles `Z_n(C) ↪ C_n` splits because every module over a field is
injective.  That is `sp-coeff`'s `moduleInjective_of_field`, and it is the **only**
genuinely field-specific input in the whole Kronecker layer — the vendored
`moduleInjective_ZMod2` proves the same thing by `fin_cases` over the two elements of `F₂`.

Nothing vendored is edited; §5 records the `rfl` bridges to the `ZMod 2` names.
-/

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace GroupApproximation
namespace CharClass

/-! ## 1. The functional of a coboundary vanishes -/

/-- **The Kronecker functional of a coboundary is zero**: `δη` evaluated on a cycle class
vanishes, because `δη(z) = η(∂z) = η(0) = 0`. -/
theorem kroneckerFunctionalOf_coboundary (K : Type) [CommRing K] (X : TopCat.{0}) (m : ℕ)
    (η : singularCochainGroup K X m)
    (hcoc : cochainCoboundary K X (m + 1) (cochainCoboundary K X m η) = 0) :
    kroneckerFunctionalOf K X (m + 1) (cochainCoboundary K X m η) hcoc = 0 := by
  apply homology_hom_extOf
  rw [kroneckerFunctionalOf_homologyπ, Limits.comp_zero,
    show cochainCoboundary K X m η = (chainCxOf K X).d (m + 1) m ≫ η from rfl,
    ← Category.assoc, HomologicalComplex.iCycles_d, Limits.zero_comp]

/-! ## 2. Linearity on cochain cycles -/

/-- Additivity content of the cycles map (its `map_add'` field). -/
theorem kroneckerFunctionalOf_iCycles_add (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (c c' : (cochainCxK K X).cycles n) :
    (kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom (c + c'))
        (cochainCoboundary_iCyclesK K X n (c + c'))).hom
      = (kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom c)
          (cochainCoboundary_iCyclesK K X n c)).hom
        + (kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom c')
            (cochainCoboundary_iCyclesK K X n c')).hom := by
  have hmap : ((cochainCxK K X).iCycles n).hom (c + c')
      = ((cochainCxK K X).iCycles n).hom c + ((cochainCxK K X).iCycles n).hom c' :=
    map_add _ _ _
  have hsum : cochainCoboundary K X n
      (((cochainCxK K X).iCycles n).hom c + ((cochainCxK K X).iCycles n).hom c') = 0 := by
    simpa only [map_add] using cochainCoboundary_iCyclesK K X n (c + c')
  have hstep : kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom (c + c'))
        (cochainCoboundary_iCyclesK K X n (c + c'))
      = kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom c)
          (cochainCoboundary_iCyclesK K X n c)
        + kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom c')
          (cochainCoboundary_iCyclesK K X n c') := by
    rw [kroneckerFunctionalOf_congr K X n hmap
      (cochainCoboundary_iCyclesK K X n (c + c')) hsum]
    exact kroneckerFunctionalOf_add K X n _ _ (cochainCoboundary_iCyclesK K X n c)
      (cochainCoboundary_iCyclesK K X n c') hsum
  exact congrArg ModuleCat.Hom.hom hstep

/-- Homogeneity content of the cycles map (its `map_smul'` field). -/
theorem kroneckerFunctionalOf_iCycles_smul (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (s : K) (c : (cochainCxK K X).cycles n) :
    (kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom (s • c))
        (cochainCoboundary_iCyclesK K X n (s • c))).hom
      = s • (kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom c)
          (cochainCoboundary_iCyclesK K X n c)).hom := by
  have hmap : ((cochainCxK K X).iCycles n).hom (s • c)
      = s • ((cochainCxK K X).iCycles n).hom c := map_smul _ _ _
  have hsmul : cochainCoboundary K X n
      (s • ((cochainCxK K X).iCycles n).hom c) = 0 := by
    simpa only [map_smul] using cochainCoboundary_iCyclesK K X n (s • c)
  have hstep : kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom (s • c))
        (cochainCoboundary_iCyclesK K X n (s • c))
      = s • kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom c)
          (cochainCoboundary_iCyclesK K X n c) := by
    rw [kroneckerFunctionalOf_congr K X n hmap
      (cochainCoboundary_iCyclesK K X n (s • c)) hsmul]
    exact kroneckerFunctionalOf_smul K X n s _ (cochainCoboundary_iCyclesK K X n c) hsmul
  exact congrArg ModuleCat.Hom.hom hstep

/-! ## 3. The classifier map -/

/-- The Kronecker functional as a `K`-linear map on the cochain cycles. -/
def kroneckerCyclesMapOf (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) :
    (cochainCxK K X).cycles n ⟶ homologyDualOf K X n :=
  ModuleCat.ofHom
    { toFun := fun c =>
        (kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom c)
          (cochainCoboundary_iCyclesK K X n c)).hom
      map_add' := kroneckerFunctionalOf_iCycles_add K X n
      map_smul' := kroneckerFunctionalOf_iCycles_smul K X n }

@[simp] theorem kroneckerCyclesMapOf_hom_apply (K : Type) [CommRing K] (X : TopCat.{0})
    (n : ℕ) (c : (cochainCxK K X).cycles n) :
    (kroneckerCyclesMapOf K X n).hom c
      = (kroneckerFunctionalOf K X n (((cochainCxK K X).iCycles n).hom c)
          (cochainCoboundary_iCyclesK K X n c)).hom := rfl

/-- The cycles map kills coboundaries, hence descends along the cohomology cokernel. -/
theorem kroneckerCyclesMapOf_toCycles (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) :
    (cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ kroneckerCyclesMapOf K X n
      = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  change (kroneckerFunctionalOf K X n
    (((cochainCxK K X).iCycles n).hom
      (((cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w)) _).hom = 0
  apply congrArg ModuleCat.Hom.hom
  apply homology_hom_extOf
  rw [kroneckerFunctionalOf_homologyπ]
  have hcochain :
      ((cochainCxK K X).iCycles n).hom
          (((cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w) =
        ((cochainCxK K X).d ((ComplexShape.up ℕ).prev n) n).hom w :=
    ConcreteCategory.congr_hom
      ((cochainCxK K X).toCycles_i ((ComplexShape.up ℕ).prev n) n) w
  change (chainCxOf K X).iCycles n ≫
      (((cochainCxK K X).iCycles n).hom
        (((cochainCxK K X).toCycles ((ComplexShape.up ℕ).prev n) n).hom w)) = 0
  rw [hcochain]
  change (chainCxOf K X).iCycles n ≫
      ((chainCxOf K X).d n ((ComplexShape.up ℕ).prev n) ≫ w) = 0
  rw [← Category.assoc, (chainCxOf K X).iCycles_d, Limits.zero_comp]

/-- **The Kronecker (evaluation) classifier** `Hⁿ(X; K) ⟶ Hom_K(Hₙ(X; K), K)`, sending
`[φ] ↦ ([z] ↦ φ(z))`. -/
def kroneckerMapOf (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) :
    cohomologyK K X n ⟶ homologyDualOf K X n :=
  ((cochainCxK K X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).desc
    (CokernelCofork.ofπ (kroneckerCyclesMapOf K X n) (kroneckerCyclesMapOf_toCycles K X n))

/-- The defining factorisation of `kroneckerMapOf` through `homologyπ`. -/
theorem kroneckerMapOf_homologyπ (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ) :
    (cochainCxK K X).homologyπ n ≫ kroneckerMapOf K X n = kroneckerCyclesMapOf K X n :=
  ((cochainCxK K X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl).fac
    (CokernelCofork.ofπ (kroneckerCyclesMapOf K X n) (kroneckerCyclesMapOf_toCycles K X n))
    WalkingParallelPair.one

/-- **Computation rule**: the classifier on the class of a cocycle is its functional. -/
theorem kroneckerMapOf_cocycleClassK (K : Type) [CommRing K] (X : TopCat.{0}) (n : ℕ)
    (φ : singularCochainGroup K X n) (hφ : cochainCoboundary K X n φ = 0) :
    (kroneckerMapOf K X n).hom (cocycleClassK K X n φ hφ)
      = (kroneckerFunctionalOf K X n φ hφ).hom := by
  unfold cocycleClassK
  rw [← ModuleCat.comp_apply, kroneckerMapOf_homologyπ, kroneckerCyclesMapOf_hom_apply]
  exact congrArg ModuleCat.Hom.hom
    (kroneckerFunctionalOf_congr K X n (iCycles_cyclesMkK K X n φ hφ) _ _)

/-! ## 4. Surjectivity, over a field -/

/-- **The cycle inclusion splits over a field.**  `iCycles : Z_n(C) ↪ C_n` is a mono with a
retraction, because every module over a field is injective (`moduleInjective_of_field`).
This is the one place in the Kronecker layer where the field is used. -/
theorem chainCxOf_iCycles_split (K : Type) [Field K] (X : TopCat.{0}) (n : ℕ) :
    ∃ s : (chainCxOf K X).X n ⟶ (chainCxOf K X).cycles n,
      (chainCxOf K X).iCycles n ≫ s = 𝟙 ((chainCxOf K X).cycles n) := by
  haveI : Module.Injective K ((chainCxOf K X).cycles n) :=
    moduleInjective_of_field K _
  haveI : CategoryTheory.Injective ((chainCxOf K X).cycles n) :=
    Module.injective_object_of_injective_module K ((chainCxOf K X).cycles n)
  exact ⟨CategoryTheory.Injective.factorThru (𝟙 _) ((chainCxOf K X).iCycles n),
    CategoryTheory.Injective.comp_factorThru _ _⟩

/-- **Surjectivity of the Kronecker classifier over a field**, the constructive direction
of the universal coefficient theorem: every functional on `Hₙ(X; K)` is `[z] ↦ φ(z)` for
some cocycle `φ`. -/
theorem kroneckerMapOf_surjective (K : Type) [Field K] (X : TopCat.{0}) (n : ℕ) :
    Function.Surjective (kroneckerMapOf K X n).hom := by
  intro g
  obtain ⟨s, hs⟩ := chainCxOf_iCycles_split K X n
  -- The cochain representing `g`: retract onto the cycles, project to homology, apply `g`.
  -- Writing it as a composite of morphisms rather than of linear maps keeps the whole
  -- argument categorical, so no element chase and no `ModuleCat.hom`/`ofHom` bookkeeping.
  have h_r_iCycles : (chainCxOf K X).iCycles n
        ≫ (s ≫ (chainCxOf K X).homologyπ n ≫ ModuleCat.ofHom g)
      = (chainCxOf K X).homologyπ n ≫ ModuleCat.ofHom g := by
    rw [← Category.assoc, hs, Category.id_comp]
  have h_phi_cocycle : cochainCoboundary K X n
      (s ≫ (chainCxOf K X).homologyπ n ≫ ModuleCat.ofHom g) = 0 := by
    show (chainCxOf K X).d (n + 1) n
        ≫ (s ≫ (chainCxOf K X).homologyπ n ≫ ModuleCat.ofHom g) = 0
    rw [← HomologicalComplex.toCycles_i (chainCxOf K X) (n + 1) n, Category.assoc,
      h_r_iCycles, ← Category.assoc, HomologicalComplex.toCycles_comp_homologyπ,
      Limits.zero_comp]
  refine ⟨cocycleClassK K X n _ h_phi_cocycle, ?_⟩
  rw [kroneckerMapOf_cocycleClassK]
  have hkf : kroneckerFunctionalOf K X n
      (s ≫ (chainCxOf K X).homologyπ n ≫ ModuleCat.ofHom g) h_phi_cocycle
      = ModuleCat.ofHom g := by
    apply homology_hom_extOf
    rw [kroneckerFunctionalOf_homologyπ]
    exact h_r_iCycles
  rw [hkf, ModuleCat.hom_ofHom]

/-! ## 5. The `ZMod 2` instance is the vendored object -/

theorem kroneckerCyclesMapOf_zmod2 (X : TopCat.{0}) (n : ℕ) :
    kroneckerCyclesMapOf (ZMod 2) X n = kroneckerCyclesMap X n := rfl

theorem kroneckerMapOf_zmod2 (X : TopCat.{0}) (n : ℕ) :
    kroneckerMapOf (ZMod 2) X n = kroneckerMap X n := rfl

end CharClass
end GroupApproximation

end
