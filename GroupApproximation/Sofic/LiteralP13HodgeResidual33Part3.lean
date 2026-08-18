import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (3, 3). -/

namespace Residual33Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![227686714, 219912663, 354811377, 180422800, 120092464, 165578772, 120695415, 65047509, 69144868]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 3 3 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 3 3 = 69150489 := by
  decide +kernel

end Residual33Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_3_3 : initialPart 3 3 3 + finalChunk 3 3 = 1592543071 := by
  have hpart : initialPart 3 3 3 =
      ∑ u : Fin 9, Residual33Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual33Part3.all u
  rw [hpart, Residual33Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
