import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationData

/-!
# Continuous tracial states for the HNN trace argument

`TensorSynchronizationData.norm_tracialState_le` proves, by the GNS
Cauchy--Schwarz argument, that every algebraically bundled tracial state on a
C-star algebra is contractive.  Here we package precisely the continuous
linear functional needed by the HNN trace comparison.
-/

namespace GroupApproximation
namespace HNNTrace

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- The continuous linear functional underlying an algebraically bundled
tracial state. -/
def tracialStateCLM (tau : TracialState A) : A →L[ℂ] ℂ :=
  LinearMap.mkContinuous tau.toLinearMap 1 fun a ↦ by
    simpa using
      Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le tau a

@[simp] theorem tracialStateCLM_apply (tau : TracialState A) (a : A) :
    tracialStateCLM tau a = tau a :=
  rfl

end

end HNNTrace
end GroupApproximation
