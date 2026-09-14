/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZeroCoordinate

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-- Deleting the apex and then taking the normalized tail recovers the base
simplex. -/
theorem coneTail_cofaceTop_zero (k : ℕ) (y : Delta k) :
    coneTail (cofaceTop k 0 y) = y := by
  ext i
  rw [coneTail_apply]
  · simp [cofaceTop_zero_succ, cofaceTop_apply_base]
  · simp [cofaceTop_apply_base]

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
