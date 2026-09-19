import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (2, 1). -/

namespace Residual21Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![486884614, 105938048, 184123852, 197428592, 155315240, 252923219, 423854243, 103515265, 213182923]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 1 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 2 1 = 91070484 := by
  decide +kernel

end Residual21Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_1_3 : initialPart 2 1 3 + finalChunk 2 1 = 2214236480 := by
  have hpart : initialPart 2 1 3 =
      ∑ u : Fin 9, Residual21Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual21Part3.all u
  rw [hpart, Residual21Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
