import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (3, 2). -/

namespace Residual32Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![239819160, 55198010, 309742511, 132493775, 241633672, 100090685, 285901462, 225759013, 202609522]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 3 2 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 3 2 = 103178781 := by
  decide +kernel

end Residual32Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_2_3 : initialPart 3 2 3 + finalChunk 3 2 = 1896426591 := by
  have hpart : initialPart 3 2 3 =
      ∑ u : Fin 9, Residual32Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual32Part3.all u
  rw [hpart, Residual32Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
