import GroupApproximation.Analysis.STW22BaseUniformTracialGauge

/-!
# Uniform two-seminorm estimates for canonical trace extension

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

abbrev G (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
    [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))] :=
  allTracesTracialTwoGauge D

abbrev M (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
    [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))] :=
  scalarPlusJSubalgebra (G D)

theorem coe_sub_M (x y : M D) :
    (((x - y : M D) : BoundedCStarSequence D)) = x.1 - y.1 := rfl

/-! ## Uniform two-seminorm estimates -/

theorem uniformTwoNorm_zero :
    uniformTwoNorm (G D) (0 : BoundedCStarSequence D) = 0 := by
  apply le_antisymm
  · exact uniformTwoNorm_le (G D) _ fun n ↦ by simp
  · exact uniformTwoNorm_nonneg (G D) _

theorem uniformTwoNorm_add_le' (x y : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x + y) ≤
      uniformTwoNorm (G D) x + uniformTwoNorm (G D) y := by
  apply uniformTwoNorm_le
  intro n
  exact ((G D).add_le n (x n) (y n)).trans
    (add_le_add (q_le_uniformTwoNorm (G D) x n)
      (q_le_uniformTwoNorm (G D) y n))

theorem uniformTwoNorm_sub_triangle (x y z : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x - z) ≤
      uniformTwoNorm (G D) (x - y) + uniformTwoNorm (G D) (y - z) := by
  apply uniformTwoNorm_le
  intro n
  exact ((G D).sub_le_sub_add_sub n (x n) (y n) (z n)).trans
    (add_le_add (q_le_uniformTwoNorm (G D) (x - y) n)
      (q_le_uniformTwoNorm (G D) (y - z) n))

theorem uniformTwoNorm_sub_comm (x y : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x - y) = uniformTwoNorm (G D) (y - x) := by
  apply le_antisymm <;> apply uniformTwoNorm_le <;> intro n
  · change (G D).q n (x n - y n) ≤ uniformTwoNorm (G D) (y - x)
    rw [(G D).sub_comm_eq n (x n) (y n)]
    exact q_le_uniformTwoNorm (G D) (y - x) n
  · change (G D).q n (y n - x n) ≤ uniformTwoNorm (G D) (x - y)
    rw [(G D).sub_comm_eq n (y n) (x n)]
    exact q_le_uniformTwoNorm (G D) (x - y) n

theorem uniformTwoNorm_smul_le (c : ℂ) (x : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (c • x) ≤ ‖c‖ * uniformTwoNorm (G D) x := by
  apply uniformTwoNorm_le
  intro n
  exact ((G D).smul_le n c (x n)).trans
    (mul_le_mul_of_nonneg_left (q_le_uniformTwoNorm (G D) x n)
      (norm_nonneg c))

theorem uniformTwoNorm_star_eq (x : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (star x) = uniformTwoNorm (G D) x := by
  apply le_antisymm
  · apply uniformTwoNorm_le
    intro n
    change (G D).q n (star (x n)) ≤ uniformTwoNorm (G D) x
    rw [(G D).star_eq]
    exact q_le_uniformTwoNorm (G D) x n
  · have h := uniformTwoNorm_le (G D) (star (star x)) fun n ↦ by
      change (G D).q n (star (star (x n))) ≤ uniformTwoNorm (G D) (star x)
      rw [(G D).star_eq]
      exact q_le_uniformTwoNorm (G D) (star x) n
    simpa using h

theorem uniformTwoNorm_mul_left_le (x y : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x * y) ≤ ‖x‖ * uniformTwoNorm (G D) y := by
  apply uniformTwoNorm_le
  intro n
  calc
    (G D).q n ((x * y) n) ≤ ‖x n‖ * (G D).q n (y n) :=
      (G D).mul_left_le n (x n) (y n)
    _ ≤ ‖x‖ * uniformTwoNorm (G D) y :=
      mul_le_mul (boundedCStarSequence_coord_norm_le D x n)
        (q_le_uniformTwoNorm (G D) y n) ((G D).nonneg n _) (norm_nonneg x)

theorem uniformTwoNorm_mul_right_le (x y : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x * y) ≤ uniformTwoNorm (G D) x * ‖y‖ := by
  apply uniformTwoNorm_le
  intro n
  calc
    (G D).q n ((x * y) n) ≤ (G D).q n (x n) * ‖y n‖ :=
      (G D).mul_right_le n (x n) (y n)
    _ ≤ uniformTwoNorm (G D) x * ‖y‖ :=
      mul_le_mul (q_le_uniformTwoNorm (G D) x n)
        (boundedCStarSequence_coord_norm_le D y n) (norm_nonneg _) 
        (uniformTwoNorm_nonneg (G D) x)

theorem norm_trace_le_tracialTwoNorm
    (tau : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    ‖tau x‖ ≤ tracialTwoNorm tau x := by
  have h := norm_apply_star_mul_le tau (1 : BaseAlgebra D) x
  simpa using h

theorem norm_trace_le_uniformTwoNorm
    (tau : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    ‖tau x‖ ≤ uniformTwoNorm (G D) x.1 :=
  (norm_trace_le_tracialTwoNorm tau x).trans
    (tracialTwoNorm_le_uniformTwoNorm_allTraces tau x)

end

end STW22CanonicalTraceExtension
end GroupApproximation
