import GroupApproximation.Analysis.STW22AntipodalBlockMeasureTrace
import GroupApproximation.Analysis.CStarStateSeparation
import GroupApproximation.Analysis.STW22AntipodalTraceBoundary
import Mathlib.Topology.Metrizable.Urysohn

/-!
# The measure--trace round trip on a projective block

This file proves that the literal RMK probability measure attached to a
block trace recovers that trace when normalized fibre traces are integrated.
-/

namespace GroupApproximation
namespace STW22AntipodalBlockTraceAffineEquiv

open MeasureTheory
open STW22
open STW22AntipodalBlockTraceClassification
open STW22AntipodalBlockTraceMeasure
open STW22AntipodalBlockMeasureTrace
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped ComplexOrder

private theorem tracialState_ext {A : Type*} [Ring A] [StarRing A]
    [Algebra Complex A] {tau sigma : TracialState A}
    (h : ∀ a, tau a = sigma a) : tau = sigma := by
  cases tau with
  | mk f hf1 hfp hft =>
    cases sigma with
    | mk g hg1 hgp hgt =>
      have hfg : f = g := LinearMap.ext h
      subst g
      rfl

/-- The real part of the descended normalized fibre trace. -/
def projectiveBlockTraceRealPart {d s : Nat} (a : RealProjectiveBlock d s) :
    CompactlySupportedContinuousMap (RP d) Real :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    { toFun := fun x => (projectiveBlockTraceFunction a x).re
      continuous_toFun := Complex.continuous_re.comp
        (projectiveBlockTraceFunction a).continuous }

/-- The imaginary part of the descended normalized fibre trace. -/
def projectiveBlockTraceImagPart {d s : Nat} (a : RealProjectiveBlock d s) :
    CompactlySupportedContinuousMap (RP d) Real :=
  CompactlySupportedContinuousMap.continuousMapEquiv
    { toFun := fun x => (projectiveBlockTraceFunction a x).im
      continuous_toFun := Complex.continuous_im.comp
        (projectiveBlockTraceFunction a).continuous }

@[simp] theorem projectiveBlockTraceRealPart_apply {d s : Nat}
    (a : RealProjectiveBlock d s) (x : RP d) :
    projectiveBlockTraceRealPart a x = (projectiveBlockTraceFunction a x).re := by
  simp [projectiveBlockTraceRealPart]

@[simp] theorem projectiveBlockTraceImagPart_apply {d s : Nat}
    (a : RealProjectiveBlock d s) (x : RP d) :
    projectiveBlockTraceImagPart a x = (projectiveBlockTraceFunction a x).im := by
  simp [projectiveBlockTraceImagPart]

/-- A real scalar centre section is self-adjoint. -/
theorem projectiveRealCenter_isSelfAdjoint {d s : Nat}
    (f : CompactlySupportedContinuousMap (RP d) Real) :
    IsSelfAdjoint (projectiveRealCenter (s := s) f) := by
  rw [isSelfAdjoint_iff]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change star ((f (proj d x) : Complex) •
      (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex)) =
    (f (proj d x) : Complex) • 1
  rw [star_smul, star_one]
  simp

/-- An actual tracial state takes real values on real scalar centre sections. -/
theorem tracialState_projectiveRealCenter_im_eq_zero {d s : Nat}
    (tau : TracialState (RealProjectiveBlock d s))
    (f : CompactlySupportedContinuousMap (RP d) Real) :
    (tau (projectiveRealCenter (s := s) f)).im = 0 := by
  let phi := HNNTrace.tracialStateCLM tau
  have hphi1 : phi 1 = 1 := by
    rw [HNNTrace.tracialStateCLM_apply, tau.apply_one]
  have hphinorm : ‖phi‖ ≤ 1 := by
    unfold phi HNNTrace.tracialStateCLM
    apply LinearMap.mkContinuous_norm_le
    norm_num
  exact CStarState.im_apply_eq_zero_of_isSelfAdjoint phi hphi1 hphinorm
    (projectiveRealCenter_isSelfAdjoint f)

/-- Splitting the normalized fibre trace into real and imaginary parts gives
the centre-valued trace exactly. -/
theorem blockCenterTrace_eq_real_add_imag {d s : Nat}
    (a : RealProjectiveBlock d s) :
    blockCenterTrace a =
      projectiveRealCenter (s := s) (projectiveBlockTraceRealPart a) +
        Complex.I • projectiveRealCenter (s := s) (projectiveBlockTraceImagPart a) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  rw [blockCenterTrace_apply]
  have hz : (((s + 1 : Nat) : Complex)⁻¹ *
      ∑ i : Fin (s + 1), a.1 x i i) =
      projectiveBlockTraceFunction a (proj d x) := by
    rw [projectiveBlockTraceFunction_proj]
    congr 1
    simp [diagonalCoefficientSum, Fin.sum_univ_succ,
      distinguishedCoefficient_apply, lowerBlockCoefficient_apply]
  rw [hz]
  change projectiveBlockTraceFunction a (proj d x) •
      (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex) =
    (projectiveRealCenter (s := s) (projectiveBlockTraceRealPart a)).1 x +
      Complex.I •
        (projectiveRealCenter (s := s) (projectiveBlockTraceImagPart a)).1 x
  rw [projectiveRealCenter_apply, projectiveRealCenter_apply]
  change projectiveBlockTraceFunction a (proj d x) •
      (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex) =
    ((projectiveBlockTraceFunction a (proj d x)).re : Complex) •
        (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex) +
      Complex.I • (((projectiveBlockTraceFunction a (proj d x)).im : Complex) •
        (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex))
  rw [smul_smul]
  nth_rewrite 1 [← Complex.re_add_im (projectiveBlockTraceFunction a (proj d x))]
  rw [add_smul]
  ring_nf

/-- The centre section associated to a real test function has that test
function as its normalized fibre trace. -/
@[simp] theorem projectiveBlockTraceFunction_projectiveRealCenter
    {d s : Nat} (f : CompactlySupportedContinuousMap (RP d) Real)
    (x : RP d) :
    projectiveBlockTraceFunction (projectiveRealCenter (s := s) f) x =
      (f x : Complex) := by
  induction x using Quotient.inductionOn with
  | _ x =>
      change projectiveBlockTraceFunction
        (projectiveRealCenter (s := s) f) (proj d x) = _
      rw [projectiveBlockTraceFunction_proj]
      simp [diagonalCoefficientSum,
        distinguishedCoefficient_apply, lowerBlockCoefficient_apply,
        projectiveRealCenter_apply]
      have hs : ((s : Complex) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero s
      field_simp [hs]
      have hxq : (Quotient.mk' x : RP d) = ⟦x⟧ :=
        Quotient.sound (Setoid.refl x)
      rw [hxq]
      ring

/-- Integrating the RMK probability measure of a block trace recovers the
trace. -/
theorem probabilityMeasureBlockTrace_blockTraceProbabilityMeasure_apply
    {d s : Nat} (tau : TracialState (RealProjectiveBlock d s))
    (a : RealProjectiveBlock d s) :
    probabilityMeasureBlockTrace (blockTraceProbabilityMeasure tau) a = tau a := by
  have hre := integral_blockTraceMeasure tau (projectiveBlockTraceRealPart a)
  have him := integral_blockTraceMeasure tau (projectiveBlockTraceImagPart a)
  have hcenter := tracialState_apply_eq_blockCenterTrace tau a
  rw [blockCenterTrace_eq_real_add_imag, tau.map_add, tau.map_smul] at hcenter
  have hrealzero := tracialState_projectiveRealCenter_im_eq_zero tau
    (projectiveBlockTraceRealPart a)
  have himagzero := tracialState_projectiveRealCenter_im_eq_zero tau
    (projectiveBlockTraceImagPart a)
  have hre' : (∫ x, (projectiveBlockTraceFunction a x).re
      ∂(blockTraceMeasure tau)) =
      (tau (projectiveRealCenter (s := s)
        (projectiveBlockTraceRealPart a))).re := by
    simpa only [projectiveBlockTraceRealPart_apply] using hre
  have him' : (∫ x, (projectiveBlockTraceFunction a x).im
      ∂(blockTraceMeasure tau)) =
      (tau (projectiveRealCenter (s := s)
        (projectiveBlockTraceImagPart a))).re := by
    simpa only [projectiveBlockTraceImagPart_apply] using him
  have hint : Integrable (projectiveBlockTraceFunction a)
      (blockTraceMeasure tau) :=
    (projectiveBlockTraceFunction a).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_univ
        (Set.subset_univ _))
  apply Complex.ext
  · rw [probabilityMeasureBlockTrace_apply]
    calc
      (∫ x, projectiveBlockTraceFunction a x
          ∂(blockTraceMeasure tau)).re =
          ∫ x, (projectiveBlockTraceFunction a x).re
            ∂(blockTraceMeasure tau) :=
        (Complex.reCLM.integral_comp_comm hint).symm
      _ = _ := by
        rw [hre']
        simpa [hrealzero, himagzero] using
          (congrArg Complex.re hcenter).symm
  · rw [probabilityMeasureBlockTrace_apply]
    calc
      (∫ x, projectiveBlockTraceFunction a x
          ∂(blockTraceMeasure tau)).im =
          ∫ x, (projectiveBlockTraceFunction a x).im
            ∂(blockTraceMeasure tau) :=
        (Complex.imCLM.integral_comp_comm hint).symm
      _ = _ := by
        rw [him']
        simpa [hrealzero, himagzero] using
          (congrArg Complex.im hcenter).symm

theorem probabilityMeasureBlockTrace_blockTraceProbabilityMeasure
    {d s : Nat} (tau : TracialState (RealProjectiveBlock d s)) :
    probabilityMeasureBlockTrace (blockTraceProbabilityMeasure tau) = tau := by
  let sigma := probabilityMeasureBlockTrace (s := s)
    (blockTraceProbabilityMeasure tau)
  apply tracialState_ext
  intro a
  exact probabilityMeasureBlockTrace_blockTraceProbabilityMeasure_apply tau a

/-- Conversely, RMK applied to the trace obtained by integration recovers
the original probability measure. -/
theorem blockTraceProbabilityMeasure_probabilityMeasureBlockTrace
    {d s : Nat} (mu : ProbabilityMeasure (RP d)) :
    blockTraceProbabilityMeasure (probabilityMeasureBlockTrace (s := s) mu) = mu := by
  apply ProbabilityMeasure.toMeasure_injective
  change blockTraceMeasure (probabilityMeasureBlockTrace (s := s) mu) =
    (mu : Measure (RP d))
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [integral_blockTraceMeasure, probabilityMeasureBlockTrace_apply]
  simp only [projectiveBlockTraceFunction_projectiveRealCenter]
  rw [integral_complex_ofReal]
  exact Complex.ofReal_re _

/-- The literal trace space of one antipodal block and the probability
simplex of its real-projective base are mutually inverse as sets. -/
def blockTraceProbabilityMeasureEquiv {d s : Nat} :
    TracialState (RealProjectiveBlock d s) ≃ ProbabilityMeasure (RP d) where
  toFun := blockTraceProbabilityMeasure
  invFun := probabilityMeasureBlockTrace (s := s)
  left_inv := probabilityMeasureBlockTrace_blockTraceProbabilityMeasure
  right_inv := blockTraceProbabilityMeasure_probabilityMeasureBlockTrace

end

end STW22AntipodalBlockTraceAffineEquiv
end GroupApproximation
