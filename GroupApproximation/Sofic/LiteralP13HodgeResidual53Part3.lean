import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (5, 3). -/

namespace Residual53Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![208738827, 190079109, 227890374, 238211282, 138177071, 158505476, 224093264, 77257752, 172536888]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 5 3 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 5 3 = 111795580 := by
  decide +kernel

end Residual53Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_3_3 : initialPart 5 3 3 + finalChunk 5 3 = 1747285623 := by
  have hpart : initialPart 5 3 3 =
      ∑ u : Fin 9, Residual53Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual53Part3.all u
  rw [hpart, Residual53Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
