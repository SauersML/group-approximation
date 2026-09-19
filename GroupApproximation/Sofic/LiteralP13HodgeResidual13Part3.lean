import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (1, 3). -/

namespace Residual13Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![150019880, 151222173, 302188503, 97102388, 202118589, 211209311, 274770193, 63898215, 111909964]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 3 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 1 3 = 91811235 := by
  decide +kernel

end Residual13Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_3_3 : initialPart 1 3 3 + finalChunk 1 3 = 1656250451 := by
  have hpart : initialPart 1 3 3 =
      ∑ u : Fin 9, Residual13Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual13Part3.all u
  rw [hpart, Residual13Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
