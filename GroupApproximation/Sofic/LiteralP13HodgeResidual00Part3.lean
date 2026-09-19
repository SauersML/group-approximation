import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (0, 0). -/

namespace Residual00Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![505460100, 110058022, 168642692, 218374553, 189904196, 210016037, 411804396, 151374799, 255700704]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 0 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 0 0 = 169654143 := by
  decide +kernel

end Residual00Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_0_3 : initialPart 0 0 3 + finalChunk 0 0 = 2390989642 := by
  have hpart : initialPart 0 0 3 =
      ∑ u : Fin 9, Residual00Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual00Part3.all u
  rw [hpart, Residual00Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
