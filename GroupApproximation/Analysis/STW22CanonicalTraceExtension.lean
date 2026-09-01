import GroupApproximation.Analysis.STW22CanonicalTraceExtensionModel

/-!
# Canonical trace extension to the bounded uniform-two completion

This file is one stage of the construction of the canonical extension of base
traces to the bounded uniform-two completion.
-/

namespace GroupApproximation
namespace STW22CanonicalTraceExtension

open Filter PolarLiftingGeneralCStar
open UniformTracialSequenceCompletion UniformTracialTwoNullIdeal
open UniformTracialCompletionIdentification
open UniformTracialBoundedCauchyQuotient
open UniformTracialGNSTwoGauge STW22Assembly
open STW22ActualTraceSpaces STW22BaseUniformTracialGauge

noncomputable section

set_option linter.unusedSectionVars false

universe u

variable {D : ℕ → Type u} [∀ n, CStarAlgebra (D n)]
  [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))]

private theorem tracialState_ext {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    {tau sigma : TracialState A} (h : ∀ a, tau a = sigma a) : tau = sigma := by
  cases tau with
  | mk f hf1 hfp hft =>
    cases sigma with
    | mk g hg1 hgp hgt =>
      have hfg : f = g := LinearMap.ext h
      subst g
      rfl

/-! ## Transport to the actual bounded Cauchy completion -/

/-- The canonical extension map between the two actual bundled trace spaces. -/
noncomputable def canonicalExtension
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (tau : TracialState (BaseAlgebra D)) :
    TracialState (BoundedUniformTwoCompletion (G D) r hr) :=
  (modelExtension tau).compStarAlgHom (realizationStarAlgEquiv (G D) hr).toStarAlgHom

@[simp] theorem canonicalExtension_apply
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (tau : TracialState (BaseAlgebra D))
    (x : BoundedUniformTwoCompletion (G D) r hr) :
    canonicalExtension hr tau x = modelExtension tau (realize (G D) hr x) := rfl

@[simp] theorem canonicalExtension_baseToCompletion_apply
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (tau : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    canonicalExtension hr tau (baseToCompletion (G D) hr x) = tau x := by
  rw [canonicalExtension_apply, realize_baseToCompletion,
    modelExtension_baseToScalarPlusJ_apply]

/-- Restricting the canonical extension gives back the original base trace. -/
theorem restrictToBase_canonicalExtension
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (tau : TracialState (BaseAlgebra D)) :
    restrictToBase (G D) hr (canonicalExtension hr tau) = tau := by
  apply tracialState_ext
  intro x
  exact canonicalExtension_baseToCompletion_apply hr tau x

/-- Every canonical extension is uniform-two continuous on the actual
Cauchy quotient. -/
theorem canonicalExtension_isCompletionUniformTwoContinuous
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (tau : TracialState (BaseAlgebra D)) :
    IsCompletionUniformTwoContinuous (G D) hr (canonicalExtension hr tau) := by
  intro x hx
  exact modelExtension_isUniformTwoContinuous tau
    (fun N ↦ realize (G D) hr (x N)) hx

/-- The canonical extension is an actual continuous extension in the sense of
the trace-space endpoint. -/
theorem canonicalExtension_isContinuousExtension
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (tau : TracialState (BaseAlgebra D)) :
    IsContinuousExtension (G D) hr (canonicalExtension hr tau) tau :=
  ⟨canonicalExtension_isCompletionUniformTwoContinuous hr tau,
    canonicalExtension_baseToCompletion_apply hr tau⟩

/-- The canonical trace extension map is injective. -/
theorem canonicalExtension_injective
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r) :
    Function.Injective (canonicalExtension (D := D) hr) := by
  intro tau sigma h
  have hres := congrArg (restrictToBase (G D) hr) h
  simpa only [restrictToBase_canonicalExtension] using hres

/-- Failure of the universal continuous-extension statement is exactly
non-surjectivity of the now-constructed canonical extension map. -/
theorem canonicalExtension_not_surjective_of_not_every
    {r : ℕ → ℝ} (hr : IsCoordinateNormComparison (G D) r)
    (h : ¬ EveryCompletionTraceIsContinuousExtension (G D) hr) :
    ¬ Function.Surjective (canonicalExtension (D := D) hr) := by
  intro hsurj
  apply h
  intro sigma
  obtain ⟨tau, rfl⟩ := hsurj sigma
  exact ⟨tau, canonicalExtension_isContinuousExtension hr tau⟩

end

end STW22CanonicalTraceExtension
end GroupApproximation
