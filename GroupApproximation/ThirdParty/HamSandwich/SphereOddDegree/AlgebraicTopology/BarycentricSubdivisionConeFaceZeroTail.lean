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
