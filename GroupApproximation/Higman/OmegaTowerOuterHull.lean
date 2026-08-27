import GroupApproximation.Higman.HNNStableHull
import GroupApproximation.Higman.OmegaTowerDescent

/-!
# Stable-hull reduction for the outer Omega scan

The outer stage of Mikaelian's Omega tower cannot use the ordinary stable
subgroup descent directly: its stage-two alphabet is not shift-stable.  The
generic stable hull gives the exact unconditional replacement and leaves one
pure base-group computation.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

/-- Every original `F₃` element in the concrete Omega subgroup belongs, at
stage two, to the least shift-stable subgroup containing `slimWBase`. -/
theorem slimPiF3Hom_mem_outerStableHull_of_mem_slimW
    {m : ℕ} {B : Set E} {x : F₃}
    (hx : slimOmegaEmb m x ∈ W (slimTower m) B) :
    slimPiF3Hom m x ∈
      HNNDescent.stableHull (slimShiftRangeEquiv m) (slimWBase m B) := by
  apply HNNDescent.mem_stableHull_of_of_mem_closure
    (slimShiftRangeEquiv m)
  change slimOmegaEmb m x ∈
    Subgroup.closure
      (HNNDescent.genSet (slimShiftRangeEquiv m) (slimWBase m B))
  exact slimW_le_outerClosure m B hx

/-- Consequently the remaining hard half of the Omega computation is exactly
the base statement that the stable hull meets the embedded `F₃` inside
`A_(omegaOp m B)`. -/
theorem slimTower_descent_of_outerStableHull
    {m : ℕ} {B : Set E}
    (hbase : ∀ x : F₃,
      slimPiF3Hom m x ∈
          HNNDescent.stableHull (slimShiftRangeEquiv m) (slimWBase m B) →
        x ∈ ASub (omegaOp m B)) :
    ∀ x : F₃, slimOmegaEmb m x ∈ W (slimTower m) B →
      x ∈ ASub (omegaOp m B) := by
  intro x hx
  exact hbase x (slimPiF3Hom_mem_outerStableHull_of_mem_slimW hx)

end Omega
end Higman
end GroupApproximation
