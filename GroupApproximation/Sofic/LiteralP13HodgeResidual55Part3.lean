import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (5, 5). -/

namespace Residual55Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![199490336, 143363943, 217912533, 127253297, 114923136, 211730918, 351908883, 154941081, 88472766]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 5 5 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 5 5 = 61221881 := by
  decide +kernel

end Residual55Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_5_3 : initialPart 5 5 3 + finalChunk 5 5 = 1671218774 := by
  have hpart : initialPart 5 5 3 =
      ∑ u : Fin 9, Residual55Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual55Part3.all u
  rw [hpart, Residual55Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
