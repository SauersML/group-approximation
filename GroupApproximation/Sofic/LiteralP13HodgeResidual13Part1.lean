import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 9--17 for residual block (1, 3). -/

namespace Residual13Part1

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![344056389, 259078930, 97095700, 178198895, 183831860, 97299854, 196070636, 91921514, 159147522]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 1 3 (finProdFinEquiv ((1 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual13Part1

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_1_3_1 : initialPart 1 3 1 = 1606701300 := by
  have hpart : initialPart 1 3 1 =
      ∑ u : Fin 9, Residual13Part1.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual13Part1.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
