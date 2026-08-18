import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (4, 2). -/

namespace Residual42Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![155206215, 137459750, 111102755, 199316319, 110976823, 121767527, 269775101, 119104304, 119832151]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 4 2 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 4 2 = 39312725 := by
  decide +kernel

end Residual42Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_2_3 : initialPart 4 2 3 + finalChunk 4 2 = 1383853670 := by
  have hpart : initialPart 4 2 3 =
      ∑ u : Fin 9, Residual42Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual42Part3.all u
  rw [hpart, Residual42Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
