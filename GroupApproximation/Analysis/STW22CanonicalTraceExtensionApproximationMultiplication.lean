import GroupApproximation.Analysis.STW22CanonicalTraceExtensionApproximationLinearStar

/-!
# Multiplication of bounded base approximations

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

/-! ## Multiplication of approximations -/

def BaseApproximation.mul {x y : M D}
    (A : BaseApproximation x) (B : BaseApproximation y) :
    BaseApproximation (x * y) where
  seq := fun k ↦ A.seq k * B.seq k
  norm_bounded := by
    obtain ⟨C, hC⟩ := A.norm_bounded
    obtain ⟨E, hE⟩ := B.norm_bounded
    refine ⟨C * E, fun k ↦ ?_⟩
    exact (norm_mul_le _ _).trans
      (mul_le_mul (hC k) (hE k) (norm_nonneg _) (by
        exact (norm_nonneg _).trans (hC k)))
  tendsto_two := by
    obtain ⟨C, hC⟩ := A.norm_bounded
    have hupper : Tendsto (fun k ↦
        uniformTwoNorm (G D)
            ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
              BoundedCStarSequence D) * ‖y‖ +
          C * uniformTwoNorm (G D)
            ((y - baseToScalarPlusJ (G D) (B.seq k) : M D) :
              BoundedCStarSequence D)) atTop (nhds 0) := by
      simpa using (A.tendsto_two.mul_const ‖y‖).add
        (B.tendsto_two.const_mul C)
    refine squeeze_zero' (Eventually.of_forall fun k ↦
      uniformTwoNorm_nonneg (G D) _) (Eventually.of_forall fun k ↦ ?_) hupper
    let a : M D := baseToScalarPlusJ (G D) (A.seq k)
    let b : M D := baseToScalarPlusJ (G D) (B.seq k)
    have hring :
        (((x * y : M D) - baseToScalarPlusJ (G D) (A.seq k * B.seq k) : M D) :
            BoundedCStarSequence D) =
          (((x - a) * y + a * (y - b) : M D) : BoundedCStarSequence D) := by
      apply congrArg Subtype.val
      change x * y - a * b = (x - a) * y + a * (y - b)
      noncomm_ring
    rw [hring]
    calc
      uniformTwoNorm (G D)
          ((((x - a) * y + a * (y - b) : M D) : BoundedCStarSequence D))
          ≤ uniformTwoNorm (G D) (((x - a) * y : M D).1) +
              uniformTwoNorm (G D) ((a * (y - b) : M D).1) :=
        uniformTwoNorm_add_le' _ _
      _ ≤ uniformTwoNorm (G D) ((x - a : M D).1) * ‖y‖ +
              ‖a‖ * uniformTwoNorm (G D) ((y - b : M D).1) :=
        add_le_add (uniformTwoNorm_mul_right_le _ _)
          (uniformTwoNorm_mul_left_le _ _)
      _ ≤ uniformTwoNorm (G D) ((x - a : M D).1) * ‖y‖ +
              C * uniformTwoNorm (G D) ((y - b : M D).1) := by
        change _ + ‖A.seq k‖ * _ ≤ _ + C * _
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (hC k)
            (uniformTwoNorm_nonneg (G D) _))

end

end STW22CanonicalTraceExtension
end GroupApproximation
