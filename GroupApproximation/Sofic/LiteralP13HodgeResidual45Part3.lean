import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (4, 5). -/

namespace Residual45Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![251285096, 126827665, 185850999, 115195462, 199034620, 138128891, 521751286, 141970658, 71147006]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 4 5 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 4 5 = 28445865 := by
  decide +kernel

end Residual45Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_5_3 : initialPart 4 5 3 + finalChunk 4 5 = 1779637548 := by
  have hpart : initialPart 4 5 3 =
      ∑ u : Fin 9, Residual45Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual45Part3.all u
  rw [hpart, Residual45Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
