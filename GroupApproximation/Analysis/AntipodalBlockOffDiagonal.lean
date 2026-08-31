import GroupApproximation.Analysis.AntipodalHomogeneousBlock

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped CStarAlgebra ComplexOrder Matrix

#check Matrix.diagonal_mul
#check Matrix.mul_diagonal
#check continuous_apply
#check ContinuousMap.continuous

/-! ## Entrywise form of the antipodal covariance -/

/-- Conjugation by the block involution multiplies the `(i,j)` entry by the
two diagonal signs. -/
theorem blockInvolution_conjugation_apply {s : ℕ}
    (a : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (i j : Fin (s + 1)) :
    (blockInvolution s * a * blockInvolution s) i j =
      blockSign i * a i j * blockSign j := by
  simp [blockInvolution, CStarMatrix.mul_apply, Matrix.mul_apply]

/-- Antipodal covariance of a real-projective block, entry by entry. -/
theorem realProjectiveBlock_entry_neg {d s : ℕ}
    (a : RealProjectiveBlock d s) (x : Sphere d)
    (i j : Fin (s + 1)) :
    a.1 (-x) i j = blockSign i * a.1 x i j * blockSign j := by
  have hcov := a.2 x
  have hentry := congrArg (fun m => m i j) hcov
  simpa only [blockInvolution_conjugation_apply] using hentry

end

end STW22
end GroupApproximation
