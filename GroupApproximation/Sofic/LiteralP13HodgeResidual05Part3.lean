import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 27--35 for residual block (0, 5). -/

namespace Residual05Part3

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![325754641, 119939107, 256119426, 151294078, 193440905, 127797119, 322486550, 138048725, 107991156]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 5 (finProdFinEquiv ((3 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

theorem final : finalChunk 0 5 = 98498859 := by
  decide +kernel

end Residual05Part3

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_5_3 : initialPart 0 5 3 + finalChunk 0 5 = 1841370566 := by
  have hpart : initialPart 0 5 3 =
      ∑ u : Fin 9, Residual05Part3.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual05Part3.all u
  rw [hpart, Residual05Part3.final]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
