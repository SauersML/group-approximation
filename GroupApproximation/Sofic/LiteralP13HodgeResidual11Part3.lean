import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (1, 1). -/

namespace Residual11Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![329191589, 113208670, 323366602, 117066754, 155874020, 94572900, 252219356, 186769554, 186750138]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 1 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 1 1 = 59825574 := by
  decide +kernel

end Residual11Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_1_3 : initialPart 1 1 3 + finalChunk 1 1 = 1818845157 := by
  have hpart : initialPart 1 1 3 =
      ∑ u : Fin 9, Residual11Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual11Part3.all u
  rw [hpart, Residual11Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
