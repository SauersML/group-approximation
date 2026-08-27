import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (3, 4). -/

namespace Residual34Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![436844896, 230039536, 213931516, 83449951, 125362787, 149291560, 134259297, 132194929, 150211477]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 3 4 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 3 4 = 90585782 := by
  decide +kernel

end Residual34Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_4_3 : initialPart 3 4 3 + finalChunk 3 4 = 1746171731 := by
  have hpart : initialPart 3 4 3 =
      ∑ u : Fin 9, Residual34Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual34Part3.all u
  rw [hpart, Residual34Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
