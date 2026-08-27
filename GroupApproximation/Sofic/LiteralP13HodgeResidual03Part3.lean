import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (0, 3). -/

namespace Residual03Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![487999772, 174874196, 209933059, 346647985, 191402474, 172174706, 673593690, 216200136, 279193183]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 3 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 0 3 = 258917352 := by
  decide +kernel

end Residual03Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_3_3 : initialPart 0 3 3 + finalChunk 0 3 = 3010936553 := by
  have hpart : initialPart 0 3 3 =
      ∑ u : Fin 9, Residual03Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual03Part3.all u
  rw [hpart, Residual03Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
