import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (2, 3). -/

namespace Residual23Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![434204217, 214322675, 363760820, 168570971, 186466323, 201430488, 228700349, 214202398, 93251293]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 3 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 2 3 = 121045054 := by
  decide +kernel

end Residual23Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_3_3 : initialPart 2 3 3 + finalChunk 2 3 = 2225954588 := by
  have hpart : initialPart 2 3 3 =
      ∑ u : Fin 9, Residual23Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual23Part3.all u
  rw [hpart, Residual23Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
