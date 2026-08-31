import GroupApproximation.Analysis.STW22BaseUniformTracialGauge

/-!
# Canonical extension of base traces to the bounded uniform-two completion

For the all-traces gauge, every tracial state of the concrete unitized
`c₀`-sum is bounded by the uniform two-seminorm.  This file uses the bounded
scalar truncations to extend such a state to `ℂ1 + J`, proves directly that
the extension is a tracial state, and transports it to the actual bounded
uniform-two Cauchy quotient.
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

private abbrev G (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
    [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))] :=
  allTracesTracialTwoGauge D

private abbrev M (D : ℕ → Type u) [∀ n, CStarAlgebra (D n)]
    [∀ n, Nontrivial (D n)] [∀ n, Nonempty (TracialState (D n))] :=
  scalarPlusJSubalgebra (G D)

private theorem coe_sub_M (x y : M D) :
    (((x - y : M D) : BoundedCStarSequence D)) = x.1 - y.1 := rfl

/-! ## Uniform two-seminorm estimates -/

private theorem uniformTwoNorm_zero :
    uniformTwoNorm (G D) (0 : BoundedCStarSequence D) = 0 := by
  apply le_antisymm
  · exact uniformTwoNorm_le (G D) _ fun n ↦ by simp
  · exact uniformTwoNorm_nonneg (G D) _

private theorem uniformTwoNorm_add_le' (x y : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x + y) ≤
      uniformTwoNorm (G D) x + uniformTwoNorm (G D) y := by
  apply uniformTwoNorm_le
  intro n
  exact ((G D).add_le n (x n) (y n)).trans
    (add_le_add (q_le_uniformTwoNorm (G D) x n)
      (q_le_uniformTwoNorm (G D) y n))

private theorem uniformTwoNorm_sub_triangle (x y z : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x - z) ≤
      uniformTwoNorm (G D) (x - y) + uniformTwoNorm (G D) (y - z) := by
  apply uniformTwoNorm_le
  intro n
  exact ((G D).sub_le_sub_add_sub n (x n) (y n) (z n)).trans
    (add_le_add (q_le_uniformTwoNorm (G D) (x - y) n)
      (q_le_uniformTwoNorm (G D) (y - z) n))

private theorem uniformTwoNorm_sub_comm (x y : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x - y) = uniformTwoNorm (G D) (y - x) := by
  apply le_antisymm <;> apply uniformTwoNorm_le <;> intro n
  · change (G D).q n (x n - y n) ≤ uniformTwoNorm (G D) (y - x)
    rw [(G D).sub_comm_eq n (x n) (y n)]
    exact q_le_uniformTwoNorm (G D) (y - x) n
  · change (G D).q n (y n - x n) ≤ uniformTwoNorm (G D) (x - y)
    rw [(G D).sub_comm_eq n (y n) (x n)]
    exact q_le_uniformTwoNorm (G D) (x - y) n

private theorem uniformTwoNorm_smul_le (c : ℂ) (x : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (c • x) ≤ ‖c‖ * uniformTwoNorm (G D) x := by
  apply uniformTwoNorm_le
  intro n
  exact ((G D).smul_le n c (x n)).trans
    (mul_le_mul_of_nonneg_left (q_le_uniformTwoNorm (G D) x n)
      (norm_nonneg c))

private theorem uniformTwoNorm_star_eq (x : BoundedCStarSequence D) :
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

private theorem uniformTwoNorm_mul_left_le (x y : BoundedCStarSequence D) :
    uniformTwoNorm (G D) (x * y) ≤ ‖x‖ * uniformTwoNorm (G D) y := by
  apply uniformTwoNorm_le
  intro n
  calc
    (G D).q n ((x * y) n) ≤ ‖x n‖ * (G D).q n (y n) :=
      (G D).mul_left_le n (x n) (y n)
    _ ≤ ‖x‖ * uniformTwoNorm (G D) y :=
      mul_le_mul (boundedCStarSequence_coord_norm_le D x n)
        (q_le_uniformTwoNorm (G D) y n) ((G D).nonneg n _) (norm_nonneg x)

private theorem uniformTwoNorm_mul_right_le (x y : BoundedCStarSequence D) :
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

private theorem norm_trace_le_tracialTwoNorm
    (tau : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    ‖tau x‖ ≤ tracialTwoNorm tau x := by
  have h := norm_apply_star_mul_le tau (1 : BaseAlgebra D) x
  simpa using h

private theorem norm_trace_le_uniformTwoNorm
    (tau : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    ‖tau x‖ ≤ uniformTwoNorm (G D) x.1 :=
  (norm_trace_le_tracialTwoNorm tau x).trans
    (tracialTwoNorm_le_uniformTwoNorm_allTraces tau x)

/-! ## Bounded base approximants -/

/-- A bounded sequence from the actual base which converges to `x` in the
uniform two-seminorm. -/
private structure BaseApproximation (x : M D) where
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

private noncomputable def chosenApproximation (x : M D) : BaseApproximation x :=
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
private noncomputable def extensionValue
    (tau : TracialState (BaseAlgebra D)) (x : M D) : ℂ :=
  Classical.choose (cauchySeq_tendsto_of_complete
    (trace_approximation_cauchy tau x (chosenApproximation x)))

private theorem chosen_trace_tendsto
    (tau : TracialState (BaseAlgebra D)) (x : M D) :
    Tendsto (fun k ↦ tau ((chosenApproximation x).seq k)) atTop
      (nhds (extensionValue tau x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete
    (trace_approximation_cauchy tau x (chosenApproximation x)))

/-- Any bounded base approximation computes the same extension value. -/
private theorem trace_tendsto_extensionValue
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

/-! ## Algebra on approximations -/

private def BaseApproximation.zero : BaseApproximation (0 : M D) where
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

private def BaseApproximation.one : BaseApproximation (1 : M D) where
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

private def BaseApproximation.add {x y : M D}
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
      apply congrArg Subtype.val
      rw [map_add]
      abel
    rw [hring]
    exact uniformTwoNorm_add_le' _ _

private def BaseApproximation.smul (c : ℂ) {x : M D}
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
      apply congrArg Subtype.val
      rw [map_smul, smul_sub]
    rw [hring]
    exact uniformTwoNorm_smul_le c _

private def BaseApproximation.star {x : M D}
    (A : BaseApproximation x) : BaseApproximation (star x) where
  seq := fun k ↦ star (A.seq k)
  norm_bounded := by
    obtain ⟨C, hC⟩ := A.norm_bounded
    exact ⟨C, fun k ↦ by simpa using hC k⟩
  tendsto_two := by
    have hfun : (fun k ↦ uniformTwoNorm (G D)
        (((star x : M D) - baseToScalarPlusJ (G D) (star (A.seq k)) : M D) :
          BoundedCStarSequence D)) =
      fun k ↦ uniformTwoNorm (G D)
        ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
          BoundedCStarSequence D) := by
      funext k
      have hring :
          (((star x : M D) - baseToScalarPlusJ (G D) (star (A.seq k)) : M D) :
              BoundedCStarSequence D) =
            star (((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
              BoundedCStarSequence D)) := by
        apply congrArg Subtype.val
        rw [map_star, star_sub]
      rw [hring, uniformTwoNorm_star_eq]
    rw [hfun]
    exact A.tendsto_two

private def BaseApproximation.mul {x y : M D}
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
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right (hC k)
            (uniformTwoNorm_nonneg (G D) _)) _

/-! ## The extended tracial state on `ℂ1 + J` -/

private theorem extensionValue_zero (tau : TracialState (BaseAlgebra D)) :
    extensionValue tau (0 : M D) = 0 := by
  exact tendsto_nhds_unique
    (trace_tendsto_extensionValue tau 0 BaseApproximation.zero)
    (by simpa using tendsto_const_nhds)

private theorem extensionValue_one (tau : TracialState (BaseAlgebra D)) :
    extensionValue tau (1 : M D) = 1 := by
  exact tendsto_nhds_unique
    (trace_tendsto_extensionValue tau 1 BaseApproximation.one)
    (by simpa using tendsto_const_nhds)

private theorem extensionValue_add (tau : TracialState (BaseAlgebra D))
    (x y : M D) : extensionValue tau (x + y) =
      extensionValue tau x + extensionValue tau y := by
  let A := chosenApproximation x
  let B := chosenApproximation y
  have hleft := trace_tendsto_extensionValue tau (x + y) (A.add B)
  have hright := (chosen_trace_tendsto tau x).add (chosen_trace_tendsto tau y)
  exact tendsto_nhds_unique hleft (by simpa using hright)

private theorem extensionValue_smul (tau : TracialState (BaseAlgebra D))
    (c : ℂ) (x : M D) : extensionValue tau (c • x) =
      c • extensionValue tau x := by
  let A := chosenApproximation x
  have hleft := trace_tendsto_extensionValue tau (c • x) (A.smul c)
  have hright := (chosen_trace_tendsto tau x).const_smul c
  exact tendsto_nhds_unique hleft (by simpa using hright)

private theorem extensionValue_star_mul_self_nonneg
    (tau : TracialState (BaseAlgebra D)) (x : M D) :
    0 ≤ extensionValue tau (star x * x) := by
  let A := chosenApproximation x
  have hlim := trace_tendsto_extensionValue tau (star x * x) (A.star.mul A)
  exact ge_of_tendsto' hlim (Eventually.of_forall fun k ↦ by
    simpa using tau.map_star_mul_self_nonneg (A.seq k))

private theorem extensionValue_mul_comm
    (tau : TracialState (BaseAlgebra D)) (x y : M D) :
    extensionValue tau (x * y) = extensionValue tau (y * x) := by
  let A := chosenApproximation x
  let B := chosenApproximation y
  have hxy := trace_tendsto_extensionValue tau (x * y) (A.mul B)
  have hyx := trace_tendsto_extensionValue tau (y * x) (B.mul A)
  have heq : (fun k ↦ tau (A.seq k * B.seq k)) =
      fun k ↦ tau (B.seq k * A.seq k) := by
    funext k
    exact tau.map_mul_comm _ _
  rw [heq] at hxy
  exact tendsto_nhds_unique hxy hyx

/-- The canonical uniform-two-continuous extension on the concrete model
`M = ℂ1 + J`. -/
noncomputable def modelExtension
    (tau : TracialState (BaseAlgebra D)) : TracialState (M D) where
  toLinearMap :=
    { toFun := extensionValue tau
      map_add' := extensionValue_add tau
      map_smul' := extensionValue_smul tau }
  map_one := extensionValue_one tau
  map_star_mul_self_nonneg := extensionValue_star_mul_self_nonneg tau
  map_mul_comm := extensionValue_mul_comm tau

@[simp] theorem modelExtension_baseToScalarPlusJ_apply
    (tau : TracialState (BaseAlgebra D)) (x : BaseAlgebra D) :
    modelExtension tau (baseToScalarPlusJ (G D) x) = tau x := by
  let A : BaseApproximation (baseToScalarPlusJ (G D) x) :=
    { seq := fun _ ↦ x
      norm_bounded := ⟨‖x‖, fun _ ↦ le_rfl⟩
      tendsto_two := by
        have hfun : (fun _ : ℕ ↦ uniformTwoNorm (G D)
            (((baseToScalarPlusJ (G D) x : M D) -
              baseToScalarPlusJ (G D) x : M D) : BoundedCStarSequence D)) =
            fun _ ↦ (0 : ℝ) := by
          funext k
          simp only [sub_self]
          exact uniformTwoNorm_zero
        rw [hfun]
        exact tendsto_const_nhds }
  exact tendsto_nhds_unique
    (trace_tendsto_extensionValue tau _ A) (by simpa using tendsto_const_nhds)

private theorem norm_modelExtension_le_uniformTwoNorm
    (tau : TracialState (BaseAlgebra D)) (x : M D) :
    ‖modelExtension tau x‖ ≤ uniformTwoNorm (G D) x.1 := by
  let A := chosenApproximation x
  have hleft : Tendsto (fun k ↦ ‖tau (A.seq k)‖) atTop
      (nhds ‖modelExtension tau x‖) := (chosen_trace_tendsto tau x).norm
  have hright : Tendsto (fun k ↦
      uniformTwoNorm (G D)
          ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
            BoundedCStarSequence D) + uniformTwoNorm (G D) x.1)
      atTop (nhds (uniformTwoNorm (G D) x.1)) := by
    simpa using A.tendsto_two.add tendsto_const_nhds
  refine le_of_tendsto_of_tendsto' hleft hright (Eventually.of_forall fun k ↦ ?_)
  calc
    ‖tau (A.seq k)‖ ≤ uniformTwoNorm (G D) (A.seq k).1 :=
      norm_trace_le_uniformTwoNorm tau _
    _ ≤ uniformTwoNorm (G D)
          ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
            BoundedCStarSequence D) + uniformTwoNorm (G D) x.1 := by
      calc
        uniformTwoNorm (G D) (A.seq k).1 =
            uniformTwoNorm (G D)
              ((baseToScalarPlusJ (G D) (A.seq k) : M D).1 - 0) := by rw [sub_zero]
        _ ≤ uniformTwoNorm (G D)
              ((baseToScalarPlusJ (G D) (A.seq k) : M D).1 - x.1) +
            uniformTwoNorm (G D) (x.1 - 0) :=
          uniformTwoNorm_sub_triangle _ _ _
        _ = uniformTwoNorm (G D)
              ((x - baseToScalarPlusJ (G D) (A.seq k) : M D) :
                BoundedCStarSequence D) + uniformTwoNorm (G D) x.1 := by
          rw [uniformTwoNorm_sub_comm, coe_sub_M, sub_zero]

/-- The model extension is sequentially continuous for the uniform
two-seminorm. -/
theorem modelExtension_isUniformTwoContinuous
    (tau : TracialState (BaseAlgebra D)) :
    IsUniformTwoContinuous (G D) (modelExtension tau) := by
  intro x hx
  refine squeeze_zero_norm (fun N ↦ ?_) hx
  exact norm_modelExtension_le_uniformTwoNorm tau (x N)

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
