import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 0--8 for residual block (2, 2). -/

namespace Residual22Part0

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![208118416, 167486313, 279610856, 377369740, 151734542, 438067472, 224873082, 298344821, 447600413]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 2 (finProdFinEquiv ((0 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual22Part0

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_2_0 : initialPart 2 2 0 = 2593205655 := by
  have hpart : initialPart 2 2 0 =
      ∑ u : Fin 9, Residual22Part0.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual22Part0.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
