import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (3, 1). -/

namespace Residual31Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![139976971, 127343554, 233824047, 147757226, 131283239, 252491146, 144287849, 228119762, 107269227]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 3 1 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 3 1 = 45509156 := by
  decide +kernel

end Residual31Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_3_1_3 : initialPart 3 1 3 + finalChunk 3 1 = 1557862177 := by
  have hpart : initialPart 3 1 3 =
      ∑ u : Fin 9, Residual31Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual31Part3.all u
  rw [hpart, Residual31Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
