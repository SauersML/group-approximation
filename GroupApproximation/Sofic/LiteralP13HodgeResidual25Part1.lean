import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 9--17 for residual block (2, 5). -/

namespace Residual25Part1

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![221826710, 167126460, 103249566, 248720758, 317599639, 125075105, 89306032, 197738650, 171638870]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 5 (finProdFinEquiv ((1 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual25Part1

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_5_1 : initialPart 2 5 1 = 1642281790 := by
  have hpart : initialPart 2 5 1 =
      ∑ u : Fin 9, Residual25Part1.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual25Part1.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
