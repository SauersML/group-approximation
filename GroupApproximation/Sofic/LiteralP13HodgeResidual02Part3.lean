import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (0, 2). -/

namespace Residual02Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![323676915, 174434929, 300929297, 180466118, 164795238, 86817189, 355379563, 143131266, 271695724]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 2 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 0 2 = 172733798 := by
  decide +kernel

end Residual02Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_2_3 : initialPart 0 2 3 + finalChunk 0 2 = 2174060037 := by
  have hpart : initialPart 0 2 3 =
      ∑ u : Fin 9, Residual02Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual02Part3.all u
  rw [hpart, Residual02Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
