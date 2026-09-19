import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricSubdivisionConeContinuity
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.BarycentricBoundaryCancellation

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace AffineBarycentricSubdivision

/-- For the coface deleting vertex zero, every successor coordinate is the
corresponding coordinate of the original simplex. -/
theorem cofaceTop_zero_succ (k : ℕ) (i : Fin (k + 1)) (y : Delta k) :
    (cofaceTop k 0 y : Fin (k + 2) → ℝ) i.succ = y i := by
  show (stdSimplex.map (S := ℝ) (Fin.succAbove 0) y : Fin (k + 2) → ℝ) i.succ = y i
  change Finsupp.mapDomain (Fin.succAbove 0)
      (Finsupp.equivFunOnFinite.symm (y : Fin (k + 1) → ℝ)) i.succ = y i
  rw [Fin.succAbove_zero, Finsupp.mapDomain_apply (Fin.succ_injective (k + 1))]
  exact congrFun (Finsupp.equivFunOnFinite.apply_symm_apply (y : Fin (k + 1) → ℝ)) i

end AffineBarycentricSubdivision
end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
