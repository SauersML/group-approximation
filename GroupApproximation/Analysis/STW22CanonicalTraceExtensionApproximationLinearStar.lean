import GroupApproximation.Analysis.STW22CanonicalTraceExtensionApproximants

/-!
# Linear and star operations on bounded base approximations

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

/-! ## Algebra on approximations -/

def BaseApproximation.zero : BaseApproximation (0 : M D) where
  seq := fun _ ↦ 0
  norm_bounded := ⟨0, fun _ ↦ by simp⟩
  tendsto_two := by
    have hfun : (fun _ : ℕ ↦ uniformTwoNorm (G D)
        (((0 : M D) - baseToScalarPlusJ (G D) (0 : BaseAlgebra D) : M D) :
          BoundedCStarSequence D)) = fun _ ↦ (0 : ℝ) := by
      funext k
      simp only [map_zero, sub_zero]
      exact uniformTwoNorm_zero
    rw [hfun]
    exact tendsto_const_nhds

def BaseApproximation.one : BaseApproximation (1 : M D) where
  seq := fun _ ↦ 1
  norm_bounded := ⟨1, fun _ ↦ by simp⟩
  tendsto_two := by
    have hfun : (fun _ : ℕ ↦ uniformTwoNorm (G D)
        (((1 : M D) - baseToScalarPlusJ (G D) (1 : BaseAlgebra D) : M D) :
          BoundedCStarSequence D)) = fun _ ↦ (0 : ℝ) := by
      funext k
      simp only [map_one, sub_self]
      exact uniformTwoNorm_zero
    rw [hfun]
    exact tendsto_const_nhds

def BaseApproximation.add {x y : M D}
    (A : BaseApproximation x) (B : BaseApproximation y) :
    BaseApproximation (x + y) where
  seq := fun k ↦ A.seq k + B.seq k
  norm_bounded := by
    obtain ⟨C, hC⟩ := A.norm_bounded
    obtain ⟨E, hE⟩ := B.norm_bounded
    exact ⟨C + E, fun k ↦ (norm_add_le _ _).trans (add_le_add (hC k) (hE k))⟩
  tendsto_two := by
    have hupper : Tendsto (fun k ↦
        uniformTwoNorm (G D)
            ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
              BoundedCStarSequence D) +
          uniformTwoNorm (G D)
            ((y - baseToScalarPlusJ (G D) (B.seq k) : M D) :
              BoundedCStarSequence D)) atTop (nhds 0) := by
      simpa using A.tendsto_two.add B.tendsto_two
    refine squeeze_zero' (Eventually.of_forall fun k ↦
      uniformTwoNorm_nonneg (G D) _) (Eventually.of_forall fun k ↦ ?_) hupper
    have hring :
        (((x + y : M D) - baseToScalarPlusJ (G D) (A.seq k + B.seq k) : M D) :
            BoundedCStarSequence D) =
          ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
            BoundedCStarSequence D) +
          ((y - baseToScalarPlusJ (G D) (B.seq k) : M D) :
            BoundedCStarSequence D) := by
      have hM :
          (x + y - baseToScalarPlusJ (G D) (A.seq k + B.seq k) : M D) =
            (x - baseToScalarPlusJ (G D) (A.seq k) : M D) +
              (y - baseToScalarPlusJ (G D) (B.seq k) : M D) := by
        rw [map_add]
        abel
      simpa using congrArg Subtype.val hM
    rw [hring]
    exact uniformTwoNorm_add_le' _ _

def BaseApproximation.smul (c : ℂ) {x : M D}
    (A : BaseApproximation x) : BaseApproximation (c • x) where
  seq := fun k ↦ c • A.seq k
  norm_bounded := by
    obtain ⟨C, hC⟩ := A.norm_bounded
    refine ⟨‖c‖ * C, fun k ↦ ?_⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC k) (norm_nonneg c)
  tendsto_two := by
    have hupper : Tendsto (fun k ↦ ‖c‖ * uniformTwoNorm (G D)
        ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
          BoundedCStarSequence D)) atTop (nhds 0) := by
      simpa using A.tendsto_two.const_mul ‖c‖
    refine squeeze_zero' (Eventually.of_forall fun k ↦
      uniformTwoNorm_nonneg (G D) _) (Eventually.of_forall fun k ↦ ?_) hupper
    have hring :
        (((c • x : M D) - baseToScalarPlusJ (G D) (c • A.seq k) : M D) :
            BoundedCStarSequence D) =
          c • (((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
            BoundedCStarSequence D)) := by
      have hM :
          (c • x - baseToScalarPlusJ (G D) (c • A.seq k) : M D) =
            c • (x - baseToScalarPlusJ (G D) (A.seq k) : M D) := by
        rw [map_smul, smul_sub]
      simpa using congrArg Subtype.val hM
    rw [hring]
    exact uniformTwoNorm_smul_le c _

def BaseApproximation.star {x : M D}
    (A : BaseApproximation x) : BaseApproximation (star x) where
  seq := fun k ↦ Star.star (A.seq k)
  norm_bounded := by
    obtain ⟨C, hC⟩ := A.norm_bounded
    exact ⟨C, fun k ↦ by simpa using hC k⟩
  tendsto_two := by
    have hfun : (fun k ↦ uniformTwoNorm (G D)
        (((Star.star x : M D) -
            baseToScalarPlusJ (G D) (Star.star (A.seq k)) : M D) :
          BoundedCStarSequence D)) =
      fun k ↦ uniformTwoNorm (G D)
        ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
          BoundedCStarSequence D) := by
      funext k
      have hring :
          (((Star.star x : M D) -
              baseToScalarPlusJ (G D) (Star.star (A.seq k)) : M D) :
              BoundedCStarSequence D) =
            Star.star (((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
              BoundedCStarSequence D)) := by
        have hM :
            (Star.star x -
                baseToScalarPlusJ (G D) (Star.star (A.seq k)) : M D) =
              Star.star
                (x - baseToScalarPlusJ (G D) (A.seq k) : M D) := by
          rw [map_star, star_sub]
        exact congrArg Subtype.val hM
      rw [hring, uniformTwoNorm_star_eq]
    rw [hfun]
    exact A.tendsto_two

end

end STW22CanonicalTraceExtension
end GroupApproximation
