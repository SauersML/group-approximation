import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 9--17 for residual block (1, 5). -/

namespace Residual15Part1

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![182822329, 321918539, 146183810, 244250420, 171006354, 163138744, 113159239, 76208923, 157277451]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 5 (finProdFinEquiv ((1 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual15Part1

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_5_1 : initialPart 1 5 1 = 1575965809 := by
  have hpart : initialPart 1 5 1 =
      ∑ u : Fin 9, Residual15Part1.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual15Part1.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
