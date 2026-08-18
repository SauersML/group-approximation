import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (0, 1). -/

namespace Residual01Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![390549844, 165642307, 183630920, 256970346, 229632481, 116430027, 478577056, 168986936, 181139148]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 1 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 0 1 = 125880049 := by
  decide +kernel

end Residual01Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_1_3 : initialPart 0 1 3 + finalChunk 0 1 = 2297439114 := by
  have hpart : initialPart 0 1 3 =
      ∑ u : Fin 9, Residual01Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual01Part3.all u
  rw [hpart, Residual01Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
