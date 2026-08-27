import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (2, 5). -/

namespace Residual25Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![429067536, 194715246, 219115583, 288082005, 294969655, 171961432, 362152930, 241552341, 102913704]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 5 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 2 5 = 115541178 := by
  decide +kernel

end Residual25Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_5_3 : initialPart 2 5 3 + finalChunk 2 5 = 2420071610 := by
  have hpart : initialPart 2 5 3 =
      ∑ u : Fin 9, Residual25Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual25Part3.all u
  rw [hpart, Residual25Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
