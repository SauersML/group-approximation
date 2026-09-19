import GroupApproximation.Analysis.AntipodalBlockNontrivial
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Separability of the real-projective blocks

The block is a closed star-subalgebra of the continuous matrix-valued
functions on a finite-dimensional sphere.  Mathlib's compact-open theorem
gives second countability of that continuous-map space once the finite matrix
target is explicitly recognized as a finite iterated function space over
`ℂ`.  Second countability then passes to the block subtype and implies
separability.
-/

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

/-- Each concrete real-projective block is separable. -/
theorem separableSpace_realProjectiveBlock (d s : ℕ) :
    TopologicalSpace.SeparableSpace (RealProjectiveBlock d s) := by
  letI : SecondCountableTopology
      (CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) := by
    change SecondCountableTopology (Fin (s + 1) → Fin (s + 1) → ℂ)
    infer_instance
  letI : SecondCountableTopology (SphereMatrixFunctions d s) := inferInstance
  letI : SecondCountableTopology (RealProjectiveBlock d s) := inferInstance
  infer_instance

instance realProjectiveBlock_separableSpace (d s : ℕ) :
    TopologicalSpace.SeparableSpace (RealProjectiveBlock d s) :=
  separableSpace_realProjectiveBlock d s

end

end STW22
end GroupApproximation
