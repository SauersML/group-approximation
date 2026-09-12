import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 18--26 for residual block (0, 1). -/

namespace Residual01Part2

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![263389526, 194054683, 557330572, 80991136, 120214286, 239819169, 313762346, 459763518, 246595526]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 0 1 (finProdFinEquiv ((2 : Fin 4), u)) = expected u

/-- The identity-containing chunk is split into eight coefficient checks. -/
def chunk25Expected : Fin 8 → Nat := ![12896236, 191278819, 93574498, 4309829, 114126063, 26588022, 13808086, 3181965]

def chunk25Check (u : Fin 8) : Prop :=
  (residualNumerator 0 1
    (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
      chunk25Expected u

mk_kernel_batched_theorem 8 chunk25Check

theorem chunk25All : ∀ u : Fin 8, chunk25Check u :=
  combine_kernel_batched_theorems% chunk25Check 8

theorem chunk25 : initialChunk 0 1 25 = 459763518 := by
  unfold initialChunk
  calc
    ∑ u : Fin 8,
        (residualNumerator 0 1
          (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
        ∑ u : Fin 8, chunk25Expected u := by
      apply Finset.sum_congr rfl
      intro u _
      exact chunk25All u
    _ = 459763518 := by decide +kernel

mk_kernel_batched_theorem_except 9 7 check

theorem check.case_7 : check 7 := by
  unfold check
  rw [show finProdFinEquiv ((2 : Fin 4), (7 : Fin 9)) =
      (25 : Fin 36) by decide +kernel]
  simpa [expected] using chunk25

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual01Part2

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_0_1_2 : initialPart 0 1 2 = 2475920762 := by
  have hpart : initialPart 0 1 2 =
      ∑ u : Fin 9, Residual01Part2.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual01Part2.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
