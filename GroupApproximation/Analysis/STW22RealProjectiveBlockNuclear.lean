import GroupApproximation.Analysis.CStarContinuousMapNuclear
import GroupApproximation.Analysis.CStarNuclearRetract
import GroupApproximation.Analysis.STW22AntipodalExpectation

/-!
# Nuclearity of the antipodal real-projective blocks

Each block is the range of the explicit completely positive contractive
antipodal expectation on a nuclear continuous matrix-valued function algebra.
-/

namespace GroupApproximation
namespace STW22

open CStarExactness
open CStarContinuousMapFiniteInterpolation

noncomputable section

/-- Every concrete real-projective block is nuclear. -/
theorem isNuclearCStarAlgebra_realProjectiveBlock (d s : ℕ) :
    IsNuclearCStarAlgebra (RealProjectiveBlock d s) := by
  apply IsNuclearCStarAlgebra.of_cpContractiveRetract
    (antipodalBlockInclusion d s (blockInvolution s)
      (blockInvolution_sq s) (blockInvolution_star s))
    (antipodalExpectation d s (blockInvolution s)
      (blockInvolution_sq s) (blockInvolution_star s))
  · exact isCompletelyPositive_antipodalExpectation d s (blockInvolution s)
      (blockInvolution_sq s) (blockInvolution_star s)
  · exact norm_antipodalExpectation_le d s (blockInvolution s)
      (blockInvolution_sq s) (blockInvolution_star s)
  · exact antipodalExpectation_inclusion d s (blockInvolution s)
      (blockInvolution_sq s) (blockInvolution_star s)
  · exact isNuclearCStarAlgebra_continuousMap
      (X := GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Sphere d)
      (B := CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)

end

end STW22
end GroupApproximation
