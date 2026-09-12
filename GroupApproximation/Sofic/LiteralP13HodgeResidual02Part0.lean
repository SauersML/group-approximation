import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 0--8 for residual block (0, 2). -/

namespace Residual02Part0

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![255478202, 242477604, 316344191, 391368958, 150885791, 203328172, 208564315, 206860890, 204851301]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 2 (finProdFinEquiv ((0 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual02Part0

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_2_0 : initialPart 0 2 0 = 2180159424 := by
  have hpart : initialPart 0 2 0 =
      ∑ u : Fin 9, Residual02Part0.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual02Part0.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
