import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (2, 2). -/

namespace Residual22Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![281455569, 232407945, 181101385, 159782569, 107745005, 139280217, 383065664, 145289743, 234863801]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 2 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 2 2 = 145289968 := by
  decide +kernel

end Residual22Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_2_3 : initialPart 2 2 3 + finalChunk 2 2 = 2010281866 := by
  have hpart : initialPart 2 2 3 =
      ∑ u : Fin 9, Residual22Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual22Part3.all u
  rw [hpart, Residual22Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
