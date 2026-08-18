import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (2, 0). -/

namespace Residual20Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![330718522, 87624428, 434787992, 205667556, 216885695, 206808233, 321866086, 93554551, 157730458]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 0 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 2 0 = 92083950 := by
  decide +kernel

end Residual20Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_0_3 : initialPart 2 0 3 + finalChunk 2 0 = 2147727471 := by
  have hpart : initialPart 2 0 3 =
      ∑ u : Fin 9, Residual20Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual20Part3.all u
  rw [hpart, Residual20Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
