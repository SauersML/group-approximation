import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 0--8 for residual block (0, 1). -/

namespace Residual01Part0

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![253347738, 246756247, 442291540, 331021206, 297443486, 363492475, 142837137, 189109489, 84924691]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 1 (finProdFinEquiv ((0 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual01Part0

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_1_0 : initialPart 0 1 0 = 2351224009 := by
  have hpart : initialPart 0 1 0 =
      ∑ u : Fin 9, Residual01Part0.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual01Part0.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
