import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 0--8 for residual block (0, 0). -/

namespace Residual00Part0

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![318517786, 393139355, 406863868, 624023378, 329826921, 371347241, 394680694, 349299800, 329965950]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 0 (finProdFinEquiv ((0 : Fin 4), u)) = expected u

mk_kernel_batched_theorem 9 check

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual00Part0

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_0_0 : initialPart 0 0 0 = 3517664993 := by
  have hpart : initialPart 0 0 0 =
      ∑ u : Fin 9, Residual00Part0.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual00Part0.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
