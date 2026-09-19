import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (4, 1). -/

namespace Residual41Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![203010618, 178179137, 165379255, 91420789, 103370988, 149568470, 277308795, 226356682, 154234687]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 4 1 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 4 1 = 98151519 := by
  decide +kernel

end Residual41Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_1_3 : initialPart 4 1 3 + finalChunk 4 1 = 1646980940 := by
  have hpart : initialPart 4 1 3 =
      ∑ u : Fin 9, Residual41Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual41Part3.all u
  rw [hpart, Residual41Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
