import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (5, 0). -/

namespace Residual50Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![331395755, 94006091, 219348731, 232172323, 177066349, 178448668, 272293111, 98966838, 146500412]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 5 0 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 5 0 = 40469299 := by
  decide +kernel

end Residual50Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_0_3 : initialPart 5 0 3 + finalChunk 5 0 = 1790667577 := by
  have hpart : initialPart 5 0 3 =
      ∑ u : Fin 9, Residual50Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual50Part3.all u
  rw [hpart, Residual50Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
