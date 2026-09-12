import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 9--17 for residual block (5, 5). -/

namespace Residual55Part1

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![136200244, 175362986, 176231284, 150237485, 223212687, 80880634, 157031196, 173326338, 294034490]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 5 5 (finProdFinEquiv ((1 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual55Part1

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_5_5_1 : initialPart 5 5 1 = 1566517344 := by
  have hpart : initialPart 5 5 1 =
      ∑ u : Fin 9, Residual55Part1.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual55Part1.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
