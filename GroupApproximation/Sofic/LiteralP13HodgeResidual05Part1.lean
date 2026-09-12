import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 9--17 for residual block (0, 5). -/

namespace Residual05Part1

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![387780438, 289055858, 193061809, 245808926, 115272923, 164962075, 112898344, 234803243, 179186698]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 5 (finProdFinEquiv ((1 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual05Part1

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_5_1 : initialPart 0 5 1 = 1922830314 := by
  have hpart : initialPart 0 5 1 =
      ∑ u : Fin 9, Residual05Part1.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual05Part1.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
