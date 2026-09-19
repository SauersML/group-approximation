import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (5, 4). -/

namespace Residual54Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![214275699, 151025248, 123257655, 264920376, 117399283, 277659501, 117715760, 181715960, 123061295]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 5 4 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 5 4 = 59475969 := by
  decide +kernel

end Residual54Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_4_3 : initialPart 5 4 3 + finalChunk 5 4 = 1630506746 := by
  have hpart : initialPart 5 4 3 =
      ∑ u : Fin 9, Residual54Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual54Part3.all u
  rw [hpart, Residual54Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
