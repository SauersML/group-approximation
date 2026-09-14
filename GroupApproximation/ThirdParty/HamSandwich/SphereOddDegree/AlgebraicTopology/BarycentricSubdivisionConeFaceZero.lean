/-
Local adaptation of the HamSandwich development at
https://github.com/akopjan/HamSandwich/tree/76202dbbb6610ffcebbccfbf7a56f833a4c2a376
Changed for this repository: namespace isolation, Lean 4.32 porting,
and local proof integration. The original license is retained in this tree.
-/
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeFaceZeroTail

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-! ## 5. Face formulas -/

/-
**Face opposite the apex.** Restricting the cone along the `0`-th coface
recovers the base simplex `τ`.
-/
theorem cone_face_zero {n k : ℕ} (v : Delta n) (τ : Delta k → Delta n) :
    (fun y : Delta k => affineConeMap v τ (cofaceTop k 0 y)) = τ := by
  ext y j
  rw [affineConeMap_coord, coneTail_cofaceTop_zero]
  simp [cofaceTop_apply_base]
end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
