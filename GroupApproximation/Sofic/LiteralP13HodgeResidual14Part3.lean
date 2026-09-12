import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (1, 4). -/

namespace Residual14Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![405376409, 75569630, 345762701, 190971945, 207065816, 261388696, 406897235, 159650965, 106599220]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 4 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 1 4 = 51595012 := by
  decide +kernel

end Residual14Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_4_3 : initialPart 1 4 3 + finalChunk 1 4 = 2210877629 := by
  have hpart : initialPart 1 4 3 =
      ∑ u : Fin 9, Residual14Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual14Part3.all u
  rw [hpart, Residual14Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
