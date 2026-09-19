import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (4, 0). -/

namespace Residual40Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![283646954, 140256977, 329678329, 134624353, 125475365, 135220714, 169338349, 185262615, 40906321]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 4 0 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 4 0 = 64055327 := by
  decide +kernel

end Residual40Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_0_3 : initialPart 4 0 3 + finalChunk 4 0 = 1608465304 := by
  have hpart : initialPart 4 0 3 =
      ∑ u : Fin 9, Residual40Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual40Part3.all u
  rw [hpart, Residual40Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
