import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (1, 5). -/

namespace Residual15Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![117465281, 167513280, 181237348, 144947336, 259928507, 119471072, 356846174, 82122346, 105954117]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 5 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 1 5 = 110200767 := by
  decide +kernel

end Residual15Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_5_3 : initialPart 1 5 3 + finalChunk 1 5 = 1645686228 := by
  have hpart : initialPart 1 5 3 =
      ∑ u : Fin 9, Residual15Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual15Part3.all u
  rw [hpart, Residual15Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
