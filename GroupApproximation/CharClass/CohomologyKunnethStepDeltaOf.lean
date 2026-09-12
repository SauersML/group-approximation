import GroupApproximation.CharClass.CohomologyKunnethStepOf
import GroupApproximation.CharClass.CohomologyDeltaNaturalOf
import GroupApproximation.CharClass.CohomologyDeltaCupOf
import GroupApproximation.Meta.AxiomGuard

/-!
# The Künneth induction step over a field

Lane `lix-coeff` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5).

Additive twin of `CohomologyKunnethStep.injective_sphereNext` with coefficients in a field `K`.
With `t₁` the suspension of `t₀`, naturality of `δ` along the sphere projection turns `pr_S^* t₁`
into `δ τ`, δ-linearity turns `δ τ ⌣ pr^* v` into `δ (τ ⌣ pr^* v)`, exactness makes `τ ⌣ pr^* v`
a sum of restrictions from the two hemispheres, and both hemispheres are `Y` through the
projection, so that sum is a pullback from `Y`.  Transporting along the band equivalence is the
hypothesis of `KnGenOf K n t₀`.

**Signs.**  δ-linearity carries no sign when the global class is on the right: with a lift
`(x_U, x_V)` of `w`, the lift of `w ⌣ b|` is `(x_U ⌣ b|, x_V ⌣ b|)`, and `d(x ⌣ b) = dx ⌣ b` for a
cocycle `b`.  Exactness at the intersection over `K` is a **sum** of honest restrictions
(`mvExactWOf`), which is what `exists_pull_prSub_of_resOf` consumes.

## Main declarations

* `KnHemi.injective_sphereNextOf` — the step.
-/

open CategoryTheory Limits TopologicalSpace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

namespace KnHemi

set_option maxHeartbeats 1000000 in
/-- **The Künneth induction step over `K`.**  If `t₀` detects classes on the base up to a
pullback, then its suspension detects them outright. -/
theorem injective_sphereNextOf (K : Type) [Field K] (n : ℕ)
    (t₀ : Hmod K (TopCat.of (Sphere n)) n) (h : KnGenOf K n t₀)
    (Y : Type) [TopologicalSpace Y] (m : ℕ) (v : Hmod K (TopCat.of Y) m)
    (hv : cup (pull (knPrS Y (n + 1)) (n + 1) (sphereNextOf K n t₀))
      (pull (knPrY Y (n + 1)) m v) = 0) : v = 0 := by
  set τ : Hmod K (TopCat.of ↥(bandSet Y n)) n :=
    pull (bandRestrict Y n) n (pull (cmap (bandToSphere n)) n t₀) with hτ
  -- naturality of `δ` identifies the suspended class
  have hdelta : (mvDeltaOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) n).hom τ
      = pull (knPrS Y (n + 1)) (n + 1) (sphereNextOf K n t₀) :=
    MVDelta.mvDeltaOf_naturality K (knPrS Y (n + 1)) (upperOpens n) (lowerOpens n)
      (upperOpens_sup_lowerOpens n) n (pull (cmap (bandToSphere n)) n t₀)
  -- δ-linearity
  have hzero : (mvDeltaOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) (n + m)).hom
      (cup τ (pull (prSub Y n (bandSet Y n)) m v)) = 0 := by
    have hb := MVDelta.mvDeltaOf_cup K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) τ
      (pull (knPrY Y (n + 1)) m v)
    rw [pull_sInclusion_knPrYOf, hdelta, hv, CharClass.cohCast_zero] at hb
    exact hb
  -- exactness at the intersection
  obtain ⟨a, b, hab⟩ := (mvExactWOf K (hemiU Y n) (hemiV Y n) (hemi_sup Y n) (n + m)
    (cup τ (pull (prSub Y n (bandSet Y n)) m v))).1 hzero
  obtain ⟨c, hc⟩ := exists_pull_prSub_of_resOf K Y n (n + m) _ a b hab
  -- transport to `Y × S^n`
  have key : cup (pull (knPrS Y n) n t₀) (pull (knPrY Y n) m v)
      = pull (knPrY Y n) (n + m) c := by
    refine pull_bandHE_injectiveOf K Y n (n + m) ?_
    rw [pull_cup, pull_bandHE_knPrSOf, pull_bandHE_knPrYOf, pull_bandHE_knPrYOf, ← hτ, hc]
  exact h Y m v c key

end KnHemi

end

/-! Audited on every build. -/

#audit_axioms KnHemi.injective_sphereNextOf

end GroupApproximation.CharClass
