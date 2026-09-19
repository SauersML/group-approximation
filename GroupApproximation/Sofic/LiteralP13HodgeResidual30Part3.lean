import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (3, 0). -/

namespace Residual30Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![167813997, 74431147, 263106589, 331264126, 239755763, 72932691, 186243149, 93361483, 189543583]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 3 0 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 3 0 = 40968773 := by
  decide +kernel

end Residual30Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_0_3 : initialPart 3 0 3 + finalChunk 3 0 = 1659421301 := by
  have hpart : initialPart 3 0 3 =
      ∑ u : Fin 9, Residual30Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual30Part3.all u
  rw [hpart, Residual30Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
