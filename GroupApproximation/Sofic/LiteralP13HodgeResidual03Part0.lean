import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 0--8 for residual block (0, 3). -/

namespace Residual03Part0

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![327941016, 297661602, 155870006, 505304306, 246752542, 285538031, 128826140, 158390225, 159386154]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 3 (finProdFinEquiv ((0 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual03Part0

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_3_0 : initialPart 0 3 0 = 2265670022 := by
  have hpart : initialPart 0 3 0 =
      ∑ u : Fin 9, Residual03Part0.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual03Part0.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
