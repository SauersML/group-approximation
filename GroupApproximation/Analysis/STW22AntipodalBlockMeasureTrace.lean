import GroupApproximation.Analysis.STW22AntipodalBlockTraceMeasure

/-!
# Traces obtained from probability measures on a projective block

The normalized fibre trace of a section descends to a continuous complex
function on real projective space.  Integrating this function against an
actual probability measure gives an actual tracial state of the block.
-/

namespace GroupApproximation
namespace STW22AntipodalBlockMeasureTrace

open MeasureTheory
open STW22
open STW22AntipodalTraceBoundary
open STW22AntipodalBlockTraceClassification
open STW22AntipodalBlockTraceMeasure
open UniformTracialGNSTwoGauge
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open Manuscript.OneSidedMFRadical.TensorSynchronizationMatrixCore

noncomputable section

open scoped ComplexOrder

/-- The normalized pointwise matrix trace of a block section, descended to
the literal real-projective base. -/
def projectiveBlockTraceFunction {d s : Nat}
    (a : RealProjectiveBlock d s) : C(RP d, Complex) where
  toFun := Quotient.lift
    (fun x : Sphere d => (((s + 1 : Nat) : Complex)⁻¹ * diagonalCoefficientSum a x))
    (by
      intro x y hxy
      rcases hxy with hxy | hxy
      · rw [hxy]
      · rw [hxy, diagonalCoefficientSum_neg])
  continuous_toFun := (proj_isQuotientMap d).continuous_iff.mpr <| by
    simpa only [Function.comp_apply, Quotient.lift_mk] using
      (continuous_const.mul (diagonalCoefficientSum a).continuous)

@[simp] theorem projectiveBlockTraceFunction_proj {d s : Nat}
    (a : RealProjectiveBlock d s) (x : Sphere d) :
    projectiveBlockTraceFunction a (proj d x) =
      (((s + 1 : Nat) : Complex)⁻¹ * diagonalCoefficientSum a x) := rfl

theorem projectiveBlockTraceFunction_eq_fibre {d s : Nat}
    (a : RealProjectiveBlock d s) (x : Sphere d) :
    projectiveBlockTraceFunction a (proj d x) = fibreTracialState d s x a := by
  rw [projectiveBlockTraceFunction_proj, fibreTracialState,
    TracialState.compStarAlgHom_apply, matrixTracialState_apply]
  simp [antipodalBlockEval, diagonalCoefficientSum, Fin.sum_univ_succ,
    distinguishedCoefficient_apply, lowerBlockCoefficient_apply,
    tracialState_complex_eq]

theorem projectiveBlockTraceFunction_eq_projectiveFibre {d s : Nat}
    (a : RealProjectiveBlock d s) (x : RP d) :
    projectiveBlockTraceFunction a x = projectiveFibreTracialState d s x a := by
  induction x using Quotient.inductionOn with
  | _ x => exact projectiveBlockTraceFunction_eq_fibre a x

theorem projectiveBlockTraceFunction_add {d s : Nat}
    (a b : RealProjectiveBlock d s) :
    projectiveBlockTraceFunction (a + b) =
      projectiveBlockTraceFunction a + projectiveBlockTraceFunction b := by
  apply ContinuousMap.ext
  intro x
  change projectiveBlockTraceFunction (a + b) x =
    projectiveBlockTraceFunction a x + projectiveBlockTraceFunction b x
  rw [projectiveBlockTraceFunction_eq_projectiveFibre,
    projectiveBlockTraceFunction_eq_projectiveFibre,
    projectiveBlockTraceFunction_eq_projectiveFibre]
  exact (projectiveFibreTracialState d s x).map_add a b

theorem projectiveBlockTraceFunction_smul {d s : Nat} (c : Complex)
    (a : RealProjectiveBlock d s) :
    projectiveBlockTraceFunction (c • a) =
      c • projectiveBlockTraceFunction a := by
  apply ContinuousMap.ext
  intro x
  change projectiveBlockTraceFunction (c • a) x =
    c * projectiveBlockTraceFunction a x
  rw [projectiveBlockTraceFunction_eq_projectiveFibre,
    projectiveBlockTraceFunction_eq_projectiveFibre]
  exact (projectiveFibreTracialState d s x).map_smul c a

theorem projectiveBlockTraceFunction_one {d s : Nat} :
    projectiveBlockTraceFunction (1 : RealProjectiveBlock d s) = 1 := by
  apply ContinuousMap.ext
  intro x
  rw [projectiveBlockTraceFunction_eq_projectiveFibre]
  exact (projectiveFibreTracialState d s x).apply_one

/-- Integrate normalized fibre traces against a probability measure. -/
def probabilityMeasureBlockTrace {d s : Nat} (mu : ProbabilityMeasure (RP d)) :
    TracialState (RealProjectiveBlock d s) where
  toLinearMap :=
    { toFun := fun a => ∫ x, projectiveBlockTraceFunction a x ∂(mu : Measure (RP d))
      map_add' := fun a b => by
        rw [projectiveBlockTraceFunction_add]
        exact integral_add
          ((projectiveBlockTraceFunction a).continuous.integrable_of_hasCompactSupport
            (isClosed_tsupport _).isCompact)
          ((projectiveBlockTraceFunction b).continuous.integrable_of_hasCompactSupport
            (isClosed_tsupport _).isCompact)
      map_smul' := fun c a => by
        rw [projectiveBlockTraceFunction_smul]
        exact integral_smul c _ }
  map_one := by
    rw [projectiveBlockTraceFunction_one]
    simp
  map_star_mul_self_nonneg := by
    intro a
    rw [Complex.nonneg_iff]
    constructor
    · rw [← integral_re]
      exact integral_nonneg fun x =>
        (Complex.nonneg_iff.mp
          ((projectiveFibreTracialState d s x).map_star_mul_self_nonneg a)).1
    · rw [← integral_im]
      apply integral_eq_zero_of_ae
      filter_upwards [] with x
      exact (Complex.nonneg_iff.mp
        ((projectiveFibreTracialState d s x).map_star_mul_self_nonneg a)).2
  map_mul_comm := by
    intro a b
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [projectiveBlockTraceFunction_eq_projectiveFibre]
    exact (projectiveFibreTracialState d s x).map_mul_comm a b

@[simp] theorem probabilityMeasureBlockTrace_apply {d s : Nat}
    (mu : ProbabilityMeasure (RP d)) (a : RealProjectiveBlock d s) :
    probabilityMeasureBlockTrace mu a =
      ∫ x, projectiveBlockTraceFunction a x ∂(mu : Measure (RP d)) := rfl

end

end STW22AntipodalBlockMeasureTrace
end GroupApproximation
