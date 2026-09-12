import GroupApproximation.CharClass.KroneckerMap
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.KroneckerNaturality

/-!
# The universal coefficient isomorphism over a field

Step 3 of the port: the classifier `kroneckerMapOf K X n` of `KroneckerMap.lean` is
injective as well as surjective over a field, hence

```text
kroneckerEquivOf K X n : Hⁿ(X; K) ≅ Hom_K(Hₙ(X; K), K).
```

Over a field the universal coefficient sequence degenerates, because `Hom_K(−, K)` is
exact; the two halves are the two directions proved here and in `KroneckerMap.lean`.

## The shape of the injectivity argument

A class whose functional vanishes is represented by a cocycle `φ` with `iCycles ≫ φ = 0`.
In degree `0` every chain is a cycle, so `iCycles` is an isomorphism and `φ = 0`.  In
degree `m+1`, `φ` vanishes on `ker d`, so it factors as `φ = η ∘ d`, which says exactly
that `φ` is the coboundary of `η` — and a coboundary has zero class.  The factorisation is
the first isomorphism theorem followed by an **extension** of a functional from a
submodule, which is where the field is used, through `moduleInjective_of_field`.

Nothing vendored is edited; §4 records the bridge to the `ZMod 2` names.
-/

open CategoryTheory AlgebraicTopology Limits
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace GroupApproximation
namespace CharClass

/-! ## 1. Functionals over a field extend and factor -/

/-- **Extension of functionals over a field.**  Every functional on a submodule extends to
the whole module, because every module over a field is injective. -/
theorem extend_functional_of_field (K : Type) [Field K] {M : Type} [AddCommGroup M]
    [Module K M] (W : Submodule K M) (f : W →ₗ[K] K) :
    ∃ g : M →ₗ[K] K, ∀ w : W, g (w : M) = f w := by
  obtain ⟨g, hg⟩ := (moduleInjective_of_field K K).out W.subtype W.injective_subtype f
  exact ⟨g, fun w => hg w⟩

/-- **A functional vanishing on `ker d` factors through `d`.**  First isomorphism theorem,
then extension along the inclusion of the range. -/
theorem factor_of_ker_le_of_field (K : Type) [Field K] {M N : Type} [AddCommGroup M]
    [Module K M] [AddCommGroup N] [Module K N]
    (d : M →ₗ[K] N) (φ : M →ₗ[K] K) (h : LinearMap.ker d ≤ LinearMap.ker φ) :
    ∃ η : N →ₗ[K] K, η.comp d = φ := by
  set φbar : (M ⧸ LinearMap.ker d) →ₗ[K] K := (LinearMap.ker d).liftQ φ h with hφbar
  set e : (M ⧸ LinearMap.ker d) ≃ₗ[K] LinearMap.range d := d.quotKerEquivRange with he
  set f0 : (LinearMap.range d) →ₗ[K] K := φbar.comp e.symm.toLinearMap with hf0
  obtain ⟨η, hη⟩ := extend_functional_of_field K (LinearMap.range d) f0
  refine ⟨η, ?_⟩
  ext x
  have hmem : d x ∈ LinearMap.range d := ⟨x, rfl⟩
  have h1 : η (d x) = f0 ⟨d x, hmem⟩ := hη ⟨d x, hmem⟩
  have h2 : e.symm ⟨d x, hmem⟩ = Submodule.Quotient.mk x := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [he, LinearMap.quotKerEquivRange_apply_mk]
  simp only [LinearMap.comp_apply, h1, hf0, LinearEquiv.coe_coe, h2, hφbar,
    Submodule.liftQ_apply]

/-- **The cycle inclusion realises the kernel of the differential.** -/
theorem mem_range_iCyclesOf_of_d (K : Type) [CommRing K] {X : TopCat.{0}} (n : ℕ)
    (x : (chainCxOf K X).X (n + 1))
    (hx : ((chainCxOf K X).d (n + 1) n).hom x = 0) :
    ∃ c : (chainCxOf K X).cycles (n + 1), ((chainCxOf K X).iCycles (n + 1)).hom c = x :=
  ⟨(chainCxOf K X).cyclesMk x n (by simp [ComplexShape.next_eq']) hx,
    (chainCxOf K X).i_cyclesMk x n (by simp [ComplexShape.next_eq']) hx⟩

/-! ## 2. Injectivity, and the isomorphism -/

/-- **Injectivity of the Kronecker classifier over a field**, the uniqueness half of the
universal coefficient theorem: a class whose functional vanishes is zero. -/
theorem kroneckerMapOf_injective (K : Type) [Field K] (X : TopCat.{0}) (n : ℕ) :
    Function.Injective (kroneckerMapOf K X n).hom := by
  rw [(ModuleCat.mono_iff_injective (kroneckerMapOf K X n)).symm, ModuleCat.mono_iff_injective]
  rw [← LinearMap.ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  intro a ha
  obtain ⟨φ, hφ, rfl⟩ := cocycleClassK_surjective K X n a
  have hkf : (kroneckerFunctionalOf K X n φ hφ).hom = 0 := by
    rw [← kroneckerMapOf_cocycleClassK K X n φ hφ]
    exact ha
  have hkf0 : kroneckerFunctionalOf K X n φ hφ = 0 := by
    apply ModuleCat.hom_ext
    rw [hkf]
    rfl
  have hiφ : (chainCxOf K X).iCycles n ≫ φ = 0 := by
    rw [← kroneckerFunctionalOf_homologyπ K X n φ hφ, hkf0, Limits.comp_zero]
  rcases n with _ | m
  · -- Degree `0`: every chain is a cycle, so `iCycles` is epi and `φ = 0`.
    haveI : Epi ((chainCxOf K X).iCycles 0) := by
      have : IsIso ((chainCxOf K X).iCycles 0) :=
        (chainCxOf K X).isIso_iCycles 0 0 (by simp [ComplexShape.next])
          ((chainCxOf K X).shape 0 0 (by simp [ComplexShape.down]))
      infer_instance
    have hφ0 : φ = 0 := by
      rw [← cancel_epi ((chainCxOf K X).iCycles 0), hiφ, Limits.comp_zero]
    rw [cocycleClassK_congr K X 0 hφ0 hφ (hφ0 ▸ hφ), cocycleClassK_zero]
  · -- Degree `m+1`: `φ` vanishes on `ker d`, so it is a coboundary.
    have hkerle : LinearMap.ker ((chainCxOf K X).d (m + 1) m).hom
        ≤ LinearMap.ker φ.hom := by
      intro x hx
      simp only [LinearMap.mem_ker] at hx ⊢
      obtain ⟨c, rfl⟩ := mem_range_iCyclesOf_of_d K m x hx
      have := congrArg (fun (t : (chainCxOf K X).cycles (m + 1) ⟶ _) => t.hom c) hiφ
      simpa [ModuleCat.hom_comp, LinearMap.comp_apply] using this
    obtain ⟨ηlin, hη⟩ := factor_of_ker_le_of_field K
      ((chainCxOf K X).d (m + 1) m).hom φ.hom hkerle
    set η : singularCochainGroup K X m := ModuleCat.ofHom ηlin with hηdef
    have hcob : φ = cochainCoboundary K X m η := by
      have hstep : cochainCoboundary K X m η = (chainCxOf K X).d (m + 1) m ≫ η := rfl
      rw [hstep]
      apply ModuleCat.hom_ext
      simp only [ModuleCat.hom_comp, hηdef]
      exact hη.symm
    rw [cocycleClassK_congr K X (m + 1) hcob hφ
        (cochainCoboundary_cochainCoboundaryK K X m η),
      cocycleClassK_coboundary_zero]

/-- The classifier is bijective over a field. -/
theorem kroneckerMapOf_bijective (K : Type) [Field K] (X : TopCat.{0}) (n : ℕ) :
    Function.Bijective (kroneckerMapOf K X n).hom :=
  ⟨kroneckerMapOf_injective K X n, kroneckerMapOf_surjective K X n⟩

/-- **The universal coefficient isomorphism over a field**:
`Hⁿ(X; K) ≅ Hom_K(Hₙ(X; K), K)`. -/
def kroneckerEquivOf (K : Type) [Field K] (X : TopCat.{0}) (n : ℕ) :
    cohomologyK K X n ≅ homologyDualOf K X n :=
  (LinearEquiv.ofBijective (kroneckerMapOf K X n).hom
    (kroneckerMapOf_bijective K X n)).toModuleIso

/-! ## 3. The dual of a vanishing homology vanishes -/

/-- If `Hₙ(X; K)` is zero then so is its dual.  Used by the contractible and sphere
vanishing statements, where homology is computed first. -/
theorem homologyDualOf_isZero_of_homology_isZero (K : Type) [CommRing K] (X : TopCat.{0})
    (k : ℕ) (h : IsZero (homologyOf K X k)) : IsZero (homologyDualOf K X k) := by
  rw [ModuleCat.isZero_iff_subsingleton] at *
  exact Subsingleton.intro fun x y => by
    ext z
    have hz : z = 0 := Subsingleton.elim z 0
    simp [hz]

/-! ## 4. The `ZMod 2` instance is the vendored object -/

theorem kroneckerEquivOf_hom_zmod2 (X : TopCat.{0}) (n : ℕ) :
    (kroneckerEquivOf (ZMod 2) X n).hom = (kroneckerEquiv X n).hom := rfl

theorem homologyDualOf_isZero_of_homology_isZero_zmod2 (X : TopCat.{0}) (k : ℕ)
    (h : IsZero (homologyZMod2 X k)) :
    IsZero (homologyDualZMod2 X k) :=
  homologyDualOf_isZero_of_homology_isZero (ZMod 2) X k h

end CharClass
end GroupApproximation

end
