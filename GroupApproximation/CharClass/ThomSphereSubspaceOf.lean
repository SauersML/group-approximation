import GroupApproximation.CharClass.ThomSphereSubspace
import GroupApproximation.CharClass.CohomologyKunnethSplitOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The relative group of a sphere-bundle pair is a cokernel, over any commutative ring

Lane `lix-thom` of the stronger LIX programme (`notes/LIX_STRONGER_PROGRAM_2026-09-10.md`
§1.5), successor of `sp-thom`.

`ThomSphereSubspace` shows at `F₂` that when the ambient space is identified with a base `Y`
and the subspace with `Y × S^n`, compatibly with the projection, the restriction to the
subspace is split injective, so the relative group is the cokernel of that restriction
(`ThomRelativeCokernel.relQuotEquiv`, already over any ring).  The splitting is a slice of
the projection, and `lix-coeff`'s `pull_knPrY_injectiveOf` supplies it over any commutative
ring.

## Main declarations

* `absToSub_injective_of_sphereOf` — the restriction is injective, over `K`.
* `relQuotEquiv_of_sphereOf` — the relative group is the cokernel, over `K`.
-/

set_option autoImplicit false

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **The restriction is injective over `K`** when the ambient is the base and the subspace
is the base crossed with a sphere, compatibly with the projections. -/
theorem absToSub_injective_of_sphereOf {K : Type} [CommRing K] {Z : TopCat.{0}} (A : Set Z)
    {Y : Type} [TopologicalSpace Y] (n : ℕ) (p : Sphere n) (m : ℕ)
    (eZ : Hmod K (TopCat.of Y) m ≃ₗ[K] Hmod K Z m)
    (eA : Hmod K (TopCat.of (Y × Sphere n)) m ≃ₗ[K] Hmod K (TopCat.of ↥A) m)
    (hcompat : ∀ c : Hmod K (TopCat.of Y) m,
      pull (sInclusion A) m (eZ c) = eA (pull (knPrY Y n) m c)) :
    Function.Injective (absToSub K A m).hom := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := eZ.surjective x
  obtain ⟨d, rfl⟩ := eZ.surjective y
  have h : pull (sInclusion A) m (eZ c) = pull (sInclusion A) m (eZ d) := hxy
  rw [hcompat, hcompat] at h
  rw [pull_knPrY_injectiveOf K Y n p m (eA.injective h)]

/-- **The relative group of such a pair is the cokernel of the restriction, over `K`.** -/
noncomputable def relQuotEquiv_of_sphereOf {K : Type} [CommRing K] {Z : TopCat.{0}}
    (A : Set Z) {Y : Type} [TopologicalSpace Y] (n : ℕ) (p : Sphere n) (m : ℕ)
    (eZ : Hmod K (TopCat.of Y) (m + 1) ≃ₗ[K] Hmod K Z (m + 1))
    (eA : Hmod K (TopCat.of (Y × Sphere n)) (m + 1) ≃ₗ[K] Hmod K (TopCat.of ↥A) (m + 1))
    (hcompat : ∀ c : Hmod K (TopCat.of Y) (m + 1),
      pull (sInclusion A) (m + 1) (eZ c) = eA (pull (knPrY Y n) (m + 1) c)) :
    ((cochainCx K (TopCat.of ↥A)).homology m ⧸ LinearMap.range (absToSub K A m).hom)
      ≃ₗ[K] relCohomology K Z A (m + 1) :=
  relQuotEquiv K Z A m (absToSub_injective_of_sphereOf A n p (m + 1) eZ eA hcompat)

/-! Audited on every build: `#audit_axioms` fails the build if a closure leaves the
classical allowlist. -/

#audit_axioms absToSub_injective_of_sphereOf

end

end GroupApproximation.CharClass
