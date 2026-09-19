import GroupApproximation.AlgTop.BundleCalculusTransport
import Mathlib.Topology.Homotopy.Basic

/-!
# Bundle calculus III: pullback, and homotopy invariance of the pullback

With the section algebra `C(X, CStarMatrix ι ι ℂ)` as the ambient algebra, the
pullback of a bundle along a continuous map of base spaces is not a construction
at all -- it is Mathlib's `ContinuousMap.compStarAlgHom'`, precomposition,
already bundled as a `StarAlgHom`.  So everything the consuming lanes need about
it is a corollary of two facts proved elsewhere:

* a homomorphic image of a projection is a projection
  (`IsStarProjection.map`);
* homomorphisms respect both equivalence relations
  (`MurrayVonNeumannEquiv.map` in `KTheory/MatrixProjection.lean`, and
  `UnitaryConj.map` next door).

That is the whole reason for insisting on one ambient algebra: pullback is free
in this one.

The theorem that is not free is the last one here.  **Homotopic maps pull back
unitarily conjugate -- so isomorphic -- bundles.**  Its proof is
`unitaryConj_of_preconnected` applied along `[0,1]`, and the only work is
turning a homotopy `C(I × X, Z)` into a *continuous path in the section
algebra*, which `ContinuousMap.curry` does with no hypotheses at all.  No
subdivision, no uniform continuity, and -- worth noting -- no compactness of the
target space `Z`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

namespace GroupApproximation
namespace BundleCalculus

open scoped ComplexOrder

section Pullback

variable {X Z W : Type*} [TopologicalSpace X] [TopologicalSpace Z] [TopologicalSpace W]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Pullback of a bundle along a map of base spaces**, `f^* P = P ∘ f`.  It is
precomposition, so it is a unital star homomorphism for free, and that is what
makes it well defined on isomorphism classes. -/
noncomputable def pullback (f : C(X, Z)) :
    C(Z, CStarMatrix ι ι ℂ) →⋆ₐ[ℂ] C(X, CStarMatrix ι ι ℂ) :=
  ContinuousMap.compStarAlgHom' ℂ (CStarMatrix ι ι ℂ) f

@[simp]
theorem pullback_apply (f : C(X, Z)) (P : C(Z, CStarMatrix ι ι ℂ)) (x : X) :
    pullback (ι := ι) f P x = P (f x) := rfl

theorem pullback_id : pullback (ι := ι) (ContinuousMap.id X) = StarAlgHom.id ℂ _ :=
  ContinuousMap.compStarAlgHom'_id ℂ (CStarMatrix ι ι ℂ)

theorem pullback_comp (g : C(Z, W)) (f : C(X, Z)) :
    pullback (ι := ι) (g.comp f) = (pullback f).comp (pullback g) :=
  ContinuousMap.compStarAlgHom'_comp ℂ (CStarMatrix ι ι ℂ) g f

/-- The pullback of a bundle is a bundle. -/
theorem isStarProjection_pullback (f : C(X, Z)) {P : C(Z, CStarMatrix ι ι ℂ)}
    (hP : IsStarProjection P) : IsStarProjection (pullback (ι := ι) f P) :=
  hP.map (pullback f)

/-- The pullback is well defined on isomorphism classes. -/
theorem murrayVonNeumannEquiv_pullback (f : C(X, Z)) {P Q : C(Z, CStarMatrix ι ι ℂ)}
    (h : MurrayVonNeumannEquiv P Q) :
    MurrayVonNeumannEquiv (pullback (ι := ι) f P) (pullback f Q) :=
  h.map (pullback f)

theorem unitaryConj_pullback (f : C(X, Z)) {P Q : C(Z, CStarMatrix ι ι ℂ)}
    (h : UnitaryConj P Q) :
    UnitaryConj (pullback (ι := ι) f P) (pullback f Q) :=
  h.map (pullback f)

end Pullback

section HomotopyInvariance

variable {X Z : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Z]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Homotopic maps pull back unitarily conjugate bundles.**

The homotopy is curried into a continuous path `I → C(X, CStarMatrix ι ι ℂ)` of
projections, and `unitaryConj_of_preconnected` finishes it, because `I` is
connected.  Note that `Z` carries no compactness hypothesis: only the base `X`
of the pulled-back bundle has to be compact, and only so that
`C(X, CStarMatrix ι ι ℂ)` is a C*-algebra. -/
theorem unitaryConj_pullback_of_homotopy {f₀ f₁ : C(X, Z)}
    (H : ContinuousMap.Homotopy f₀ f₁) {P : C(Z, CStarMatrix ι ι ℂ)}
    (hP : IsStarProjection P) :
    UnitaryConj (pullback (ι := ι) f₀ P) (pullback f₁ P) := by
  -- `P` is a projection pointwise, which is all the path needs.
  have hmul : ∀ z : Z, P z * P z = P z := by
    intro z
    simpa using DFunLike.congr_fun (hP.isIdempotentElem : P * P = P) z
  have hstar : ∀ z : Z, star (P z) = P z := by
    intro z
    simpa using DFunLike.congr_fun (hP.isSelfAdjoint.star_eq : star P = P) z
  obtain ⟨F, hFdef⟩ : ∃ F : C(unitInterval × X, CStarMatrix ι ι ℂ),
      F = P.comp H.toContinuousMap := ⟨_, rfl⟩
  have hFapply : ∀ (t : unitInterval) (x : X), F.curry t x = P (H (t, x)) := by
    intro t x
    rw [hFdef]
    rfl
  have hproj : ∀ t : unitInterval, IsStarProjection (F.curry t) := by
    intro t
    constructor
    · show F.curry t * F.curry t = F.curry t
      ext x
      rw [ContinuousMap.mul_apply, hFapply]
      exact hmul _
    · show star (F.curry t) = F.curry t
      ext x
      rw [ContinuousMap.star_apply, hFapply]
      exact hstar _
  have hcont : Continuous (fun t : unitInterval => F.curry t) := map_continuous F.curry
  have key := unitaryConj_of_preconnected hcont hproj 0 1
  have h0 : F.curry (0 : unitInterval) = pullback (ι := ι) f₀ P := by
    ext x
    rw [hFapply, pullback_apply, H.apply_zero]
  have h1 : F.curry (1 : unitInterval) = pullback (ι := ι) f₁ P := by
    ext x
    rw [hFapply, pullback_apply, H.apply_one]
  rwa [h0, h1] at key

/-- Bundle-isomorphism form: **homotopic maps pull back isomorphic bundles.**
This is the statement every characteristic-class argument in the campaign
ultimately rests on. -/
theorem murrayVonNeumannEquiv_pullback_of_homotopy {f₀ f₁ : C(X, Z)}
    (H : ContinuousMap.Homotopy f₀ f₁) {P : C(Z, CStarMatrix ι ι ℂ)}
    (hP : IsStarProjection P) :
    MurrayVonNeumannEquiv (pullback (ι := ι) f₀ P) (pullback f₁ P) :=
  (unitaryConj_pullback_of_homotopy H hP).murrayVonNeumannEquiv
    (isStarProjection_pullback f₀ hP)

/-- The `Homotopic` form, for callers who have only the existence of a
homotopy. -/
theorem murrayVonNeumannEquiv_pullback_of_homotopic {f₀ f₁ : C(X, Z)}
    (h : f₀.Homotopic f₁) {P : C(Z, CStarMatrix ι ι ℂ)} (hP : IsStarProjection P) :
    MurrayVonNeumannEquiv (pullback (ι := ι) f₀ P) (pullback f₁ P) := by
  obtain ⟨H⟩ := h
  exact murrayVonNeumannEquiv_pullback_of_homotopy H hP

end HomotopyInvariance

end BundleCalculus
end GroupApproximation
