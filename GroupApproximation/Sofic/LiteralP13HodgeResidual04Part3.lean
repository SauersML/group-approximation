import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (0, 4). -/

namespace Residual04Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![423804752, 127414522, 281504671, 93258888, 237222437, 98380628, 364263359, 168545334, 227414321]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 4 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 0 4 = 97670360 := by
  decide +kernel

end Residual04Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_4_3 : initialPart 0 4 3 + finalChunk 0 4 = 2119479272 := by
  have hpart : initialPart 0 4 3 =
      ∑ u : Fin 9, Residual04Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual04Part3.all u
  rw [hpart, Residual04Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
