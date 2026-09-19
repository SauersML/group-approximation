import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (4, 4). -/

namespace Residual44Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![488080679, 149050923, 287180539, 241016098, 98657623, 212014374, 271115097, 167551873, 120984589]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 4 4 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 4 4 = 36559071 := by
  decide +kernel

end Residual44Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_4_4_3 : initialPart 4 4 3 + finalChunk 4 4 = 2072210866 := by
  have hpart : initialPart 4 4 3 =
      ∑ u : Fin 9, Residual44Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual44Part3.all u
  rw [hpart, Residual44Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
