import GroupApproximation.CharClass.CohomologyContractible
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# The complement of a point in a sphere is contractible

Stereographic projection from `v` is an open partial homeomorphism of the unit
sphere onto the orthogonal complement `(ℝ ∙ v)ᗮ` with source `{v}ᶜ` and target
everything.  So `S^n ∖ {p}` is homeomorphic to a real vector space, hence
contractible, and its reduced mod-2 cohomology vanishes.

This is the base case of the punctured-product recursion `H^k(P ∖ pt; F₂) = 0`
that lane `cc-thom` runs to show that `j^* : H^{2r}(N, N ∖ z) → H^{2r}(N)` is an
isomorphism.

## Main declarations

* `spherePunctureHomeo` — `S(E) ∖ {v} ≃ₜ (ℝ ∙ v)ᗮ`.
* `contractibleSpace_sphere_compl` — `S^n ∖ {p}` is contractible.
* `sphere_compl_cohomology_isZero` — `H^k(S^n ∖ {p}; F₂) = 0` for `k ≥ 1`.
-/

open CategoryTheory Metric
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- **Stereographic projection as a homeomorphism.**  The complement of a unit
vector `v` in the unit sphere of a real inner product space is homeomorphic to
the orthogonal complement of `v`. -/
def spherePunctureHomeo {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v : E} (hv : ‖v‖ = 1) :
    ↥((stereographic hv).source) ≃ₜ ((ℝ ∙ v)ᗮ) :=
  (stereographic hv).toHomeomorphSourceTarget.trans (Homeomorph.Set.univ _)

theorem contractibleSpace_stereographic_source {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v : E} (hv : ‖v‖ = 1) :
    ContractibleSpace ↥((stereographic hv).source) :=
  (spherePunctureHomeo hv).contractibleSpace

/-- **The complement of a point of `S^n` is contractible.** -/
theorem contractibleSpace_sphere_compl (n : ℕ) (p : Sphere n) :
    ContractibleSpace ↥({p}ᶜ : Set (Sphere n)) := by
  have hv : ‖(p : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp p.2
  haveI := contractibleSpace_stereographic_source hv
  have hsrc : (stereographic hv).source = ({p}ᶜ : Set (Sphere n)) := by
    rw [stereographic_source]
  exact (Homeomorph.setCongr hsrc).symm.contractibleSpace

/-- **`H^k(S^n ∖ {p}; F₂) = 0` for `k ≥ 1`.** -/
theorem sphere_compl_cohomology_isZero (n : ℕ) (p : Sphere n) (k : ℕ) (hk : 1 ≤ k) :
    Limits.IsZero (Hmod2 (TopCat.of ↥({p}ᶜ : Set (Sphere n))) k) :=
  haveI := contractibleSpace_sphere_compl n p
  cohomology_isZero_of_contractible _ k hk

/-- `H^0(S^n ∖ {p}; F₂) ≃ₗ F₂`. -/
def sphere_compl_cohZeroEquiv (n : ℕ) (p : Sphere n) :
    Hmod2 (TopCat.of ↥({p}ᶜ : Set (Sphere n))) 0 ≃ₗ[ZMod 2] ZMod 2 :=
  haveI := contractibleSpace_sphere_compl n p
  cohZeroEquivOfContractible _

end

end GroupApproximation.CharClass
