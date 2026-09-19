import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (5, 2). -/

namespace Residual52Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![157417813, 149926409, 145657489, 280223914, 164222330, 111982986, 279290681, 79656213, 128896099]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 5 2 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 5 2 = 78331689 := by
  decide +kernel

end Residual52Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_2_3 : initialPart 5 2 3 + finalChunk 5 2 = 1575605623 := by
  have hpart : initialPart 5 2 3 =
      ∑ u : Fin 9, Residual52Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual52Part3.all u
  rw [hpart, Residual52Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
