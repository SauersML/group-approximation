import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (5, 1). -/

namespace Residual51Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![349612626, 131524147, 256109580, 120864684, 134928450, 307430088, 93746672, 185185837, 127612507]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 5 1 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 5 1 = 25061239 := by
  decide +kernel

end Residual51Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_1_3 : initialPart 5 1 3 + finalChunk 5 1 = 1732075830 := by
  have hpart : initialPart 5 1 3 =
      ∑ u : Fin 9, Residual51Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual51Part3.all u
  rw [hpart, Residual51Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
