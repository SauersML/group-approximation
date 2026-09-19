import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (1, 0). -/

namespace Residual10Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![243363460, 67092993, 269451190, 337471738, 116648654, 168868509, 274733082, 129215332, 151590417]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 0 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 1 0 = 66277262 := by
  decide +kernel

end Residual10Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_0_3 : initialPart 1 0 3 + finalChunk 1 0 = 1824712637 := by
  have hpart : initialPart 1 0 3 =
      ∑ u : Fin 9, Residual10Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual10Part3.all u
  rw [hpart, Residual10Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
