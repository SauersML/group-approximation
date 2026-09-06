import GroupApproximation.CharClass.ThomRelativeCokernel
import GroupApproximation.CharClass.ThomKunnethNatural

/-!
# A pair whose subspace is a product with a sphere

Lane `cc-thom` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.3 Step C, hypothesis 6).

`ThomRelativeCokernel.lean` shows that a pair whose restriction is injective in
every degree has its relative group equal to the cokernel of that restriction.
This file supplies the injectivity in the case the sphere route needs, and reads
off the consequence.

The situation: the ambient contracts onto a base `Y`, the subspace is `Y × Sⁿ`,
and the two identifications are compatible with the projection to `Y`.  Then the
restriction is, in those coordinates, pullback along the projection — which is
**split injective**, because a slice retracts the projection
(`pull_knPrY_injective`).  Nothing else about the pair is used: no Künneth of
pairs, no contractibility of `Y`, no local triviality.

The compatibility is taken at the level of `pull` rather than as a commuting
square of spaces, so a caller may supply either a strict square or a homotopy
one, whichever their geometry gives.

## Main declarations

* `absToSub_injective_of_sphere` — the restriction is injective.
* `relQuotEquiv_of_sphere` — hence the relative group is the cokernel.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **The restriction is injective** when the ambient is the base and the
subspace is the base crossed with a sphere, compatibly with the projections.

In those coordinates the restriction *is* pullback along the projection, and a
slice retracts the projection, so it is split injective. -/
theorem absToSub_injective_of_sphere {Z : TopCat.{0}} (A : Set Z)
    {Y : Type} [TopologicalSpace Y] (n : ℕ) (p : Sphere n) (m : ℕ)
    (eZ : Hmod2 (TopCat.of Y) m ≃ₗ[ZMod 2] Hmod2 Z m)
    (eA : Hmod2 (TopCat.of (Y × Sphere n)) m ≃ₗ[ZMod 2] Hmod2 (TopCat.of ↥A) m)
    (hcompat : ∀ c : Hmod2 (TopCat.of Y) m,
      pull (sInclusion A) m (eZ c) = eA (pull (knPrY Y n) m c)) :
    Function.Injective (absToSub (ZMod 2) A m).hom := by
  intro x y hxy
  obtain ⟨c, rfl⟩ := eZ.surjective x
  obtain ⟨d, rfl⟩ := eZ.surjective y
  rw [absToSub_eq_cohPullback, cohPullback_apply_eq, cohPullback_apply_eq,
    hcompat, hcompat] at hxy
  rw [pull_knPrY_injective Y n p m (eA.injective hxy)]

/-- **The relative group of such a pair is the cokernel of the restriction.**
`ThomRelativeCokernel.relQuotEquiv` fed by the injectivity above. -/
noncomputable def relQuotEquiv_of_sphere {Z : TopCat.{0}} (A : Set Z)
    {Y : Type} [TopologicalSpace Y] (n : ℕ) (p : Sphere n) (m : ℕ)
    (eZ : Hmod2 (TopCat.of Y) (m + 1) ≃ₗ[ZMod 2] Hmod2 Z (m + 1))
    (eA : Hmod2 (TopCat.of (Y × Sphere n)) (m + 1) ≃ₗ[ZMod 2] Hmod2 (TopCat.of ↥A) (m + 1))
    (hcompat : ∀ c : Hmod2 (TopCat.of Y) (m + 1),
      pull (sInclusion A) (m + 1) (eZ c) = eA (pull (knPrY Y n) (m + 1) c)) :
    ((cochainCx (ZMod 2) (TopCat.of ↥A)).homology m
        ⧸ LinearMap.range (absToSub (ZMod 2) A m).hom)
      ≃ₗ[ZMod 2] relCohomology (ZMod 2) Z A (m + 1) :=
  relQuotEquiv (ZMod 2) Z A m
    (absToSub_injective_of_sphere A n p (m + 1) eZ eA hcompat)

end

end GroupApproximation.CharClass
