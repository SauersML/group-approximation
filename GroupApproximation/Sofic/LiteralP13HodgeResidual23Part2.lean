import GroupApproximation.Sofic.LiteralP13HodgeCertificateCore
import GroupApproximation.Meta.BatchedKernelChecks

namespace GroupApproximation
namespace LiteralP13HodgeCertificate

/-! Batched kernel checks 18--26 for residual block (2, 3). -/

namespace Residual23Part2

/-- Expected chunk totals; these numerals are data, not trusted equalities. -/
def expected : Fin 9 → Nat := ![389215573, 349586579, 355937713, 222078362, 223944490, 94029742, 290803966, 456983238, 223639960]

/-- One independently kernel-checked chunk equality. -/
def check (u : Fin 9) : Prop :=
  initialChunk 2 3 (finProdFinEquiv ((2 : Fin 4), u)) = expected u

/-- The identity-containing chunk is split into eight coefficient checks. -/
def chunk25Expected : Fin 8 → Nat := ![40540963, 132884849, 122736390, 20730271, 30089352, 91561132, 14444918, 3995363]

def chunk25Check (u : Fin 8) : Prop :=
  (residualNumerator 2 3
    (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
      chunk25Expected u

mk_kernel_batched_theorem 8 chunk25Check

theorem chunk25All : ∀ u : Fin 8, chunk25Check u :=
  combine_kernel_batched_theorems% chunk25Check 8

theorem chunk25 : initialChunk 2 3 25 = 456983238 := by
  unfold initialChunk
  calc
    ∑ u : Fin 8,
        (residualNumerator 2 3
          (Fin.castAdd 5 (finProdFinEquiv ((25 : Fin 36), u)))).natAbs =
        ∑ u : Fin 8, chunk25Expected u := by
      apply Finset.sum_congr rfl
      intro u _
      exact chunk25All u
    _ = 456983238 := by decide +kernel

mk_kernel_batched_theorem_except 9 7 check

theorem check.case_7 : check 7 := by
  unfold check
  rw [show finProdFinEquiv ((2 : Fin 4), (7 : Fin 9)) =
      (25 : Fin 36) by decide +kernel]
  simpa [expected] using chunk25

theorem all : ∀ u : Fin 9, check u :=
  combine_kernel_batched_theorems% check 9

end Residual23Part2

/-- Exact subtotal for this independently checked residual part. -/
theorem residual_part_sum_2_3_2 : initialPart 2 3 2 = 2606219623 := by
  have hpart : initialPart 2 3 2 =
      ∑ u : Fin 9, Residual23Part2.expected u := by
    unfold initialPart
    apply Finset.sum_congr rfl
    intro u _
    exact Residual23Part2.all u
  rw [hpart]
  decide +kernel

end LiteralP13HodgeCertificate
end GroupApproximation
