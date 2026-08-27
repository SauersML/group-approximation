import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (3, 5). -/

namespace Residual35Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![304840540, 92997787, 208438334, 197783748, 133957941, 199628442, 210186067, 172960870, 99697515]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 3 5 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 3 5 = 145771692 := by
  decide +kernel

end Residual35Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_5_3 : initialPart 3 5 3 + finalChunk 3 5 = 1766262936 := by
  have hpart : initialPart 3 5 3 =
      ∑ u : Fin 9, Residual35Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual35Part3.all u
  rw [hpart, Residual35Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
