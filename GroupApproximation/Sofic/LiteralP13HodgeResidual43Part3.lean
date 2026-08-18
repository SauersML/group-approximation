import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (4, 3). -/

namespace Residual43Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![381380295, 157288113, 306526994, 270524039, 206544457, 150858787, 171832237, 127479617, 79844080]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 4 3 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 4 3 = 91168040 := by
  decide +kernel

end Residual43Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_3_3 : initialPart 4 3 3 + finalChunk 4 3 = 1943446659 := by
  have hpart : initialPart 4 3 3 =
      ∑ u : Fin 9, Residual43Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual43Part3.all u
  rw [hpart, Residual43Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
