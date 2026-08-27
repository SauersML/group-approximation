import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (2, 4). -/

namespace Residual24Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![325769861, 142506775, 153442338, 122467945, 243767297, 145220013, 322567034, 199614930, 171246492]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 4 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 2 4 = 129511605 := by
  decide +kernel

end Residual24Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_4_3 : initialPart 2 4 3 + finalChunk 2 4 = 1956114290 := by
  have hpart : initialPart 2 4 3 =
      ∑ u : Fin 9, Residual24Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual24Part3.all u
  rw [hpart, Residual24Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
