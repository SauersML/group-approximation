import GroupApproximation.Analysis.STW22AntipodalBlockData
import GroupApproximation.Analysis.STW22BaseUniformTracialGauge
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.Hausdorff
import Mathlib.Topology.OnePoint

/-!
# The concrete boundary space for the antipodal counterexample

The extreme boundary expected for the unitized `c₀` sum of antipodal blocks
is the one-point compactification of the countable disjoint union of their
real-projective base spaces.  This file defines that literal space, supplies
its missing countability instance, and descends normalized fibre traces from
the sphere to real projective space.  No abstract affine identification is
used.
-/

namespace GroupApproximation
namespace STW22AntipodalTraceBoundary

open STW22
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open Manuscript.OneSidedMFRadical.TensorSynchronizationMatrixCore

noncomputable section

open scoped ComplexOrder

/-- Real projective space inherits second countability from its open quotient
map from the sphere. -/
instance rpSecondCountableTopology (d : ℕ) : SecondCountableTopology (RP d) :=
  TopologicalSpace.Quotient.secondCountableTopology (proj_isOpenMap d)

/-- The literal compact boundary space of the counterexample. -/
abbrev AntipodalTraceBoundary : Type :=
  OnePoint (Σ n : ℕ, RP (antipodalBlockDimension n))

instance : CompactSpace AntipodalTraceBoundary := by infer_instance
instance : T2Space AntipodalTraceBoundary := by infer_instance
instance : SecondCountableTopology AntipodalTraceBoundary := by infer_instance

/-- Normalized matrix trace is invariant under the antipodal conjugation, so
the sphere-indexed fibre traces agree at antipodal points. -/
theorem fibreTracialState_neg (d s : ℕ) (x : Sphere d) :
    fibreTracialState d s (-x) = fibreTracialState d s x := by
  apply TracialState.ext
  intro a
  change (matrixTracialState complexTracialState (Fin (s + 1)) inferInstance)
      (a.1 (-x)) =
    (matrixTracialState complexTracialState (Fin (s + 1)) inferInstance)
      (a.1 x)
  rw [a.2 x]
  let τ := matrixTracialState complexTracialState (Fin (s + 1)) inferInstance
  calc
    τ (projectiveInvolution s * a.1 x * projectiveInvolution s) =
        τ (projectiveInvolution s *
          (projectiveInvolution s * a.1 x)) := by
      rw [τ.map_mul_comm]
      simp only [mul_assoc]
    _ = τ (a.1 x) := by
      rw [← mul_assoc, projectiveInvolution_sq, one_mul]

/-- The normalized fibre trace indexed by a point of real projective space. -/
def projectiveFibreTracialState (d s : ℕ) :
    RP d → TracialState (RealProjectiveBlock d s) :=
  Quotient.lift (fibreTracialState d s) fun x y hxy ↦ by
    rcases hxy with hxy | hxy
    · simpa [hxy]
    · subst y
      exact fibreTracialState_neg d s x

@[simp] theorem projectiveFibreTracialState_proj
    (d s : ℕ) (x : Sphere d) :
    projectiveFibreTracialState d s (proj d x) = fibreTracialState d s x :=
  rfl

/-- A finite boundary point gives the corresponding actual tracial state of
the concrete block. -/
def finiteBoundaryBlockTrace
    (z : Σ n : ℕ, RP (antipodalBlockDimension n)) :
    TracialState (AntipodalCounterexampleBlock z.1) :=
  projectiveFibreTracialState (antipodalBlockDimension z.1)
    (antipodalBlockSize z.1) z.2

end

end STW22AntipodalTraceBoundary
end GroupApproximation
