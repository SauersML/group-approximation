import GroupApproximation.Analysis.STW22AntipodalBlockTraceClassification
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Measures representing traces on a real-projective block

This file transports an actual tracial state on a concrete antipodal block
to a literal regular Borel probability measure on its real-projective base.
The construction is direct: real functions on projective space are pulled
back to even scalar sections, and real Riesz--Markov--Kakutani is applied to
the resulting positive functional.
-/

namespace GroupApproximation
namespace STW22AntipodalBlockTraceMeasure

open MeasureTheory
open STW22
open STW22AntipodalTraceBoundary
open STW22AntipodalBlockTraceClassification
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped ComplexOrder

/-- Pull a real compactly supported continuous function on projective space
back to an even complex continuous function on the sphere. -/
def projectiveRealLift {d : Nat}
    (f : CompactlySupportedContinuousMap (RP d) Real) : C(Sphere d, Complex) where
  toFun x := (f (proj d x) : Complex)
  continuous_toFun := Complex.continuous_ofReal.comp
    (f.continuous_toFun.comp (proj d).continuous)

@[simp] theorem projectiveRealLift_apply {d : Nat}
    (f : CompactlySupportedContinuousMap (RP d) Real) (x : Sphere d) :
    projectiveRealLift f x = (f (proj d x) : Complex) := rfl

theorem projectiveRealLift_neg {d : Nat}
    (f : CompactlySupportedContinuousMap (RP d) Real) (x : Sphere d) :
    projectiveRealLift f (-x) = projectiveRealLift f x := by
  change (f (proj d (-x)) : Complex) = f (proj d x)
  rw [proj_neg]

/-- A real test function on projective space, embedded as an even central
scalar section of the block. -/
def projectiveRealCenter {d s : Nat}
    (f : CompactlySupportedContinuousMap (RP d) Real) :
    RealProjectiveBlock d s :=
  evenScalarElement (s := s) (projectiveRealLift f) (projectiveRealLift_neg f)

@[simp] theorem projectiveRealCenter_apply {d s : Nat}
    (f : CompactlySupportedContinuousMap (RP d) Real) (x : Sphere d) :
    (projectiveRealCenter (s := s) f).1 x = (f (proj d x) : Complex) • 1 := rfl

theorem projectiveRealCenter_add {d s : Nat}
    (f g : CompactlySupportedContinuousMap (RP d) Real) :
    projectiveRealCenter (s := s) (f + g) =
      projectiveRealCenter f + projectiveRealCenter g := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  simp [projectiveRealCenter, projectiveRealLift, add_smul]

theorem projectiveRealCenter_smul {d s : Nat} (r : Real)
    (f : CompactlySupportedContinuousMap (RP d) Real) :
    projectiveRealCenter (s := s) (r • f) =
      (r : Complex) • projectiveRealCenter f := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change ((r * f (proj d x) : Real) : Complex) •
      (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex) =
    (r : Complex) • ((f (proj d x) : Complex) • 1)
  rw [smul_smul]
  norm_num

theorem projectiveRealCenter_sub {d s : Nat}
    (f g : CompactlySupportedContinuousMap (RP d) Real) :
    projectiveRealCenter (s := s) (f - g) =
      projectiveRealCenter f - projectiveRealCenter g := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change ((f (proj d x) - g (proj d x) : Real) : Complex) •
      (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex) =
    (f (proj d x) : Complex) • 1 - (g (proj d x) : Complex) • 1
  have hcast : ((f (proj d x) - g (proj d x) : Real) : Complex) =
      (f (proj d x) : Complex) - (g (proj d x) : Complex) := by norm_num
  rw [hcast, sub_smul]

/-- A pointwise nonnegative test function gives a positive scalar section. -/
theorem tracialState_projectiveRealCenter_nonneg {d s : Nat}
    (tau : TracialState (RealProjectiveBlock d s))
    (f : CompactlySupportedContinuousMap (RP d) Real) (hf : 0 ≤ f) :
    0 ≤ (tau (projectiveRealCenter (s := s) f)).re := by
  let q : C(Sphere d, Complex) :=
    { toFun := fun x => (Real.sqrt (f (proj d x)) : Complex)
      continuous_toFun := Complex.continuous_ofReal.comp
        (Real.continuous_sqrt.comp
          (f.continuous_toFun.comp (proj d).continuous)) }
  have hqneg : forall x : Sphere d, q (-x) = q x := by
    intro x
    change (Real.sqrt (f (proj d (-x))) : Complex) =
      Real.sqrt (f (proj d x))
    rw [proj_neg]
  let b : RealProjectiveBlock d s := evenScalarElement (s := s) q hqneg
  have hsq : projectiveRealCenter (s := s) f = star b * b := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    have hfx : 0 ≤ f (proj d x) :=
      (CompactlySupportedContinuousMap.le_def.mp hf) (proj d x)
    have hsqrt : Real.sqrt (f (proj d x)) * Real.sqrt (f (proj d x)) =
        f (proj d x) := by
      simpa [pow_two] using Real.sq_sqrt hfx
    change ((f (proj d x) : Real) : Complex) •
        (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex) =
      star ((Real.sqrt (f (proj d x)) : Complex) • 1) *
        ((Real.sqrt (f (proj d x)) : Complex) • 1)
    rw [star_smul, star_one]
    simp only [RCLike.star_def, Complex.conj_ofReal, smul_mul_smul,
      one_mul]
    have hcomplex := congrArg (fun t : Real => (t : Complex) •
      (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex)) hsqrt.symm
    convert hcomplex using 1
    all_goals norm_num
  rw [hsq]
  exact (tau.map_star_mul_self_nonneg b).1

/-- The positive real-linear functional induced by a block trace on its
literal real-projective base. -/
def blockTraceRieszFunctional {d s : Nat}
    (tau : TracialState (RealProjectiveBlock d s)) :
    CompactlySupportedContinuousMap (RP d) Real →ₚ[Real] Real where
  toFun f := (tau (projectiveRealCenter (s := s) f)).re
  map_add' f g := by
    rw [projectiveRealCenter_add, tau.map_add, Complex.add_re]
  map_smul' r f := by
    rw [projectiveRealCenter_smul, tau.map_smul]
    simp
  monotone' := by
    intro f g hfg
    have hnonneg := tracialState_projectiveRealCenter_nonneg tau (g - f)
      (sub_nonneg.mpr hfg)
    rw [projectiveRealCenter_sub, tau.map_sub, Complex.sub_re] at hnonneg
    exact sub_nonneg.mp hnonneg

@[simp] theorem blockTraceRieszFunctional_apply {d s : Nat}
    (tau : TracialState (RealProjectiveBlock d s))
    (f : CompactlySupportedContinuousMap (RP d) Real) :
    blockTraceRieszFunctional tau f =
      (tau (projectiveRealCenter (s := s) f)).re := rfl

/-- The literal regular Borel measure representing a block tracial state. -/
def blockTraceMeasure {d s : Nat}
    (tau : TracialState (RealProjectiveBlock d s)) : Measure (RP d) :=
  RealRMK.rieszMeasure (blockTraceRieszFunctional tau)

instance blockTraceMeasure_isFinite {d s : Nat}
    (tau : TracialState (RealProjectiveBlock d s)) :
    IsFiniteMeasure (blockTraceMeasure tau) := by
  unfold blockTraceMeasure
  infer_instance

instance blockTraceMeasure_regular {d s : Nat}
    (tau : TracialState (RealProjectiveBlock d s)) :
    (blockTraceMeasure tau).Regular := by
  unfold blockTraceMeasure
  infer_instance

/-- RMK representation of a block trace on every real central test function. -/
theorem integral_blockTraceMeasure {d s : Nat}
    (tau : TracialState (RealProjectiveBlock d s))
    (f : CompactlySupportedContinuousMap (RP d) Real) :
    ∫ x, f x ∂blockTraceMeasure tau =
      (tau (projectiveRealCenter (s := s) f)).re := by
  exact RealRMK.integral_rieszMeasure (blockTraceRieszFunctional tau) f

end

end STW22AntipodalBlockTraceMeasure
end GroupApproximation
