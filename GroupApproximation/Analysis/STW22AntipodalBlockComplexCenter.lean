import GroupApproximation.Analysis.STW22AntipodalBlockTraceAffineEquiv

/-!
# Complex centre sections of projective blocks

Every complex continuous function on real projective space is realized as
the normalized fibre trace of a central section of the concrete antipodal
block.  This supplies the separating test functions for the reverse global
measure--trace round trip.
-/

namespace GroupApproximation
namespace STW22AntipodalBlockComplexCenter

open STW22
open STW22AntipodalBlockMeasureTrace
open STW22AntipodalBlockTraceClassification
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- Pull a complex function on projective space back to an even function on
the sphere. -/
def projectiveComplexLift {d : Nat} (f : C(RP d, Complex)) :
    C(Sphere d, Complex) := f.comp (proj d)

@[simp] theorem projectiveComplexLift_apply {d : Nat}
    (f : C(RP d, Complex)) (x : Sphere d) :
    projectiveComplexLift f x = f (proj d x) := rfl

theorem projectiveComplexLift_neg {d : Nat}
    (f : C(RP d, Complex)) (x : Sphere d) :
    projectiveComplexLift f (-x) = projectiveComplexLift f x := by
  simp only [projectiveComplexLift_apply, proj_neg]

/-- The scalar central block section associated to a complex projective
function. -/
def projectiveComplexCenter {d s : Nat} (f : C(RP d, Complex)) :
    RealProjectiveBlock d s :=
  evenScalarElement (s := s) (projectiveComplexLift f)
    (projectiveComplexLift_neg f)

@[simp] theorem projectiveComplexCenter_apply {d s : Nat}
    (f : C(RP d, Complex)) (x : Sphere d) :
    (projectiveComplexCenter (s := s) f).1 x =
      f (proj d x) •
        (1 : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) Complex) := rfl

/-- Normalized fibre trace is exactly inverse to the complex central-section
construction. -/
@[simp] theorem projectiveBlockTraceFunction_projectiveComplexCenter
    {d s : Nat} (f : C(RP d, Complex)) (x : RP d) :
    projectiveBlockTraceFunction (projectiveComplexCenter (s := s) f) x =
      f x := by
  induction x using Quotient.inductionOn with
  | _ x =>
      change projectiveBlockTraceFunction
        (projectiveComplexCenter (s := s) f) (proj d x) = _
      rw [projectiveBlockTraceFunction_proj]
      simp [diagonalCoefficientSum, projectiveComplexCenter_apply]
      have hs : ((s : Complex) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero s
      field_simp [hs]
      have hxq : (Quotient.mk' x : RP d) = ⟦x⟧ :=
        Quotient.sound (Setoid.refl x)
      rw [hxq]
      ring

end

end STW22AntipodalBlockComplexCenter
end GroupApproximation
