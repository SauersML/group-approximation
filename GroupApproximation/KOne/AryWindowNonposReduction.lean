import GroupApproximation.KOne.AryWindowNonnegReduction
import GroupApproximation.KOne.AryThetaStable
import GroupApproximation.Meta.AxiomGuard

/-!
# Nonpositive windows die, at arbitrary arity

`KOne/WindowNonposReduction.lean` for `L_k(1,d)`, through the transpose anti-automorphism:
a unit with value in the degree window `[-N-1, 0]` transposes to one with value in
`[0, N+1]`, which is a central scalar modulo the stably elementary units, and membership in
`centralClassGroup` transfers back along the involution.
-/

namespace GroupApproximation
namespace AryLeavitt

open CompleteMatrixFamily MatrixDiagonalization

variable (k : Type) [Field k] (d : ℕ)

/-- **Nonpositive-window units are central scalars modulo the stably elementary units.** -/
theorem window_nonpos_mem_centralClassGroup (hd : 2 ≤ d) (N : ℕ)
    (u : (AryLeavittAlgebra k d)ˣ)
    (hu : (u : AryLeavittAlgebra k d) ∈
      Submodule.span k ((family k d).degreeMonomials (-(N : ℤ) - 1) 0)) :
    u ∈ centralClassGroup (AryLeavittAlgebra k d) := by
  have hθ : ((thetaUnit k d u : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) ∈
      Submodule.span k ((family k d).degreeMonomials 0 ((N : ℤ) + 1)) := by
    rw [thetaUnit_val]
    have h1 := thetaHat_mem_span_degree k d hu
    refine (family k d).span_degreeMonomials_mono ?_ ?_ h1 <;> omega
  have hθH := window_nonneg_mem_centralClassGroup k d hd N (thetaUnit k d u) hθ
  exact (thetaUnit_mem_centralClassGroup_iff k d u).mp hθH

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.window_nonpos_mem_centralClassGroup
