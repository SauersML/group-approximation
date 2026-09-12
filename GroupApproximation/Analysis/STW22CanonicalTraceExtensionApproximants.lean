import GroupApproximation.Analysis.STW22CanonicalTraceExtensionEstimates

/-!
# Bounded base approximations

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

/-! ## Bounded base approximants -/

/-- A bounded sequence from the actual base which converges to `x` in the
uniform two-seminorm. -/
structure BaseApproximation (x : M D) where
  seq : ℕ → BaseAlgebra D
  norm_bounded : ∃ C : ℝ, ∀ k, ‖seq k‖ ≤ C
  tendsto_two : Tendsto (fun k ↦ uniformTwoNorm (G D)
    ((x - baseToScalarPlusJ (G D) (seq k) : M D) :
      BoundedCStarSequence D)) atTop (nhds 0)

private theorem exists_baseApproximation (x : M D) :
    Nonempty (BaseApproximation x) := by
  obtain ⟨a, C, hA, hC, -, hconv⟩ :=
    exists_uniformTwoCauchy_scalarTruncations (G D)
      (mem_scalarPlusJSubalgebra.1 x.2)
  let b : ℕ → BaseAlgebra D := fun k ↦
    ⟨a k, (mem_baseAlgebra_iff _).2 (hA k)⟩
  refine ⟨⟨b, ⟨C, fun k ↦ hC k⟩, ?_⟩⟩
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨K, hK⟩ := hconv (ε / 2) (half_pos hε)
  filter_upwards [eventually_ge_atTop K] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (uniformTwoNorm_nonneg (G D) _)]
  apply lt_of_le_of_lt (uniformTwoNorm_le (G D) _ fun n ↦ ?_)
    (half_lt_self hε)
  change (G D).q n (x.1 n - a k n) ≤ ε / 2
  exact (hK k hk n).le

noncomputable def chosenApproximation (x : M D) : BaseApproximation x :=
  Classical.choice (exists_baseApproximation x)

private theorem trace_approximation_cauchy
    (tau : TracialState (BaseAlgebra D)) (x : M D)
    (A : BaseApproximation x) : CauchySeq (fun k ↦ tau (A.seq k)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hsmall := Metric.tendsto_nhds.mp A.tendsto_two (ε / 4) (by positivity)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hsmall
  refine ⟨K, fun k hk l hl ↦ ?_⟩
  have hk' := hK k hk
  have hl' := hK l hl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (uniformTwoNorm_nonneg (G D) _)] at hk' hl'
  rw [dist_eq_norm, ← tau.map_sub]
  calc
    ‖tau (A.seq k - A.seq l)‖
        ≤ uniformTwoNorm (G D) (A.seq k - A.seq l).1 :=
      norm_trace_le_uniformTwoNorm tau _
    _ ≤ uniformTwoNorm (G D)
          ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
            BoundedCStarSequence D) +
        uniformTwoNorm (G D)
          ((x - baseToScalarPlusJ (G D) (A.seq l) : M D) :
            BoundedCStarSequence D) := by
      calc
        uniformTwoNorm (G D) (A.seq k - A.seq l).1 =
            uniformTwoNorm (G D)
              ((baseToScalarPlusJ (G D) (A.seq k) : M D).1 -
                (baseToScalarPlusJ (G D) (A.seq l) : M D).1) := rfl
        _ ≤ uniformTwoNorm (G D)
              ((baseToScalarPlusJ (G D) (A.seq k) : M D).1 - x.1) +
            uniformTwoNorm (G D)
              (x.1 - (baseToScalarPlusJ (G D) (A.seq l) : M D).1) :=
          uniformTwoNorm_sub_triangle _ _ _
        _ = uniformTwoNorm (G D)
              ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
                BoundedCStarSequence D) +
            uniformTwoNorm (G D)
              ((x - baseToScalarPlusJ (G D) (A.seq l) : M D) :
                BoundedCStarSequence D) := by
          rw [uniformTwoNorm_sub_comm, coe_sub_M, coe_sub_M]
    _ < ε := by linarith

/-- The value of the canonical extension on the concrete model `ℂ1 + J`. -/
noncomputable def extensionValue
    (tau : TracialState (BaseAlgebra D)) (x : M D) : ℂ :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (trace_approximation_cauchy tau x (chosenApproximation x)))

theorem chosen_trace_tendsto
    (tau : TracialState (BaseAlgebra D)) (x : M D) :
    Tendsto (fun k ↦ tau ((chosenApproximation x).seq k)) atTop
      (nhds (extensionValue tau x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (trace_approximation_cauchy tau x (chosenApproximation x)))

/-- Any bounded base approximation computes the same extension value. -/
theorem trace_tendsto_extensionValue
    (tau : TracialState (BaseAlgebra D)) (x : M D)
    (A : BaseApproximation x) :
    Tendsto (fun k ↦ tau (A.seq k)) atTop (nhds (extensionValue tau x)) := by
  let B := chosenApproximation x
  have hdiff : Tendsto (fun k ↦ tau (A.seq k) - tau (B.seq k)) atTop
      (nhds 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    have hA := Metric.tendsto_nhds.mp A.tendsto_two (ε / 4) (by positivity)
    have hB := Metric.tendsto_nhds.mp B.tendsto_two (ε / 4) (by positivity)
    filter_upwards [hA, hB] with k hk hbk
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (uniformTwoNorm_nonneg (G D) _)] at hk hbk
    rw [dist_zero_right, ← tau.map_sub]
    calc
      ‖tau (A.seq k - B.seq k)‖
          ≤ uniformTwoNorm (G D) (A.seq k - B.seq k).1 :=
        norm_trace_le_uniformTwoNorm tau _
      _ ≤ uniformTwoNorm (G D)
            ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
              BoundedCStarSequence D) +
          uniformTwoNorm (G D)
            ((x - baseToScalarPlusJ (G D) (B.seq k) : M D) :
              BoundedCStarSequence D) := by
        calc
          uniformTwoNorm (G D) (A.seq k - B.seq k).1 =
              uniformTwoNorm (G D)
                ((baseToScalarPlusJ (G D) (A.seq k) : M D).1 -
                  (baseToScalarPlusJ (G D) (B.seq k) : M D).1) := rfl
          _ ≤ uniformTwoNorm (G D)
                ((baseToScalarPlusJ (G D) (A.seq k) : M D).1 - x.1) +
              uniformTwoNorm (G D)
                (x.1 - (baseToScalarPlusJ (G D) (B.seq k) : M D).1) :=
            uniformTwoNorm_sub_triangle _ _ _
          _ = uniformTwoNorm (G D)
                ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
                  BoundedCStarSequence D) +
              uniformTwoNorm (G D)
                ((x - baseToScalarPlusJ (G D) (B.seq k) : M D) :
                  BoundedCStarSequence D) := by
            rw [uniformTwoNorm_sub_comm, coe_sub_M, coe_sub_M]
      _ < ε := by linarith
  have hsum := hdiff.add (chosen_trace_tendsto tau x)
  dsimp only [B] at hsum
  simpa only [sub_add_cancel, zero_add] using hsum

end

end STW22CanonicalTraceExtension
end GroupApproximation
